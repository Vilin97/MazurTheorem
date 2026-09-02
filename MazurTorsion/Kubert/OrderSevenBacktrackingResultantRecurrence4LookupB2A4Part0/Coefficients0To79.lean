/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2A4Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B2A4 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A4_coeff_0
  recurrence4A4_coeff_1
  recurrence4A4_coeff_10
  recurrence4A4_coeff_100
  recurrence4A4_coeff_101
  recurrence4A4_coeff_102
  recurrence4A4_coeff_103
  recurrence4A4_coeff_104
  recurrence4A4_coeff_105
  recurrence4A4_coeff_106
  recurrence4A4_coeff_107
  recurrence4A4_coeff_108
  recurrence4A4_coeff_109
  recurrence4A4_coeff_11
  recurrence4A4_coeff_110
  recurrence4A4_coeff_111
  recurrence4A4_coeff_112
  recurrence4A4_coeff_113
  recurrence4A4_coeff_114
  recurrence4A4_coeff_115
  recurrence4A4_coeff_116
  recurrence4A4_coeff_117
  recurrence4A4_coeff_118
  recurrence4A4_coeff_119
  recurrence4A4_coeff_12
  recurrence4A4_coeff_120
  recurrence4A4_coeff_121
  recurrence4A4_coeff_122
  recurrence4A4_coeff_123
  recurrence4A4_coeff_124
  recurrence4A4_coeff_125
  recurrence4A4_coeff_126
  recurrence4A4_coeff_127
  recurrence4A4_coeff_128
  recurrence4A4_coeff_129
  recurrence4A4_coeff_13
  recurrence4A4_coeff_130
  recurrence4A4_coeff_131
  recurrence4A4_coeff_132
  recurrence4A4_coeff_133
  recurrence4A4_coeff_134
  recurrence4A4_coeff_135
  recurrence4A4_coeff_136
  recurrence4A4_coeff_137
  recurrence4A4_coeff_138
  recurrence4A4_coeff_139
  recurrence4A4_coeff_14
  recurrence4A4_coeff_140
  recurrence4A4_coeff_141
  recurrence4A4_coeff_142
  recurrence4A4_coeff_143
  recurrence4A4_coeff_144
  recurrence4A4_coeff_145
  recurrence4A4_coeff_146
  recurrence4A4_coeff_147
  recurrence4A4_coeff_148
  recurrence4A4_coeff_149
  recurrence4A4_coeff_15
  recurrence4A4_coeff_150
  recurrence4A4_coeff_151
  recurrence4A4_coeff_152
  recurrence4A4_coeff_153
  recurrence4A4_coeff_154
  recurrence4A4_coeff_155

attribute [local simp]
  recurrence4A4_coeff_156
  recurrence4A4_coeff_157
  recurrence4A4_coeff_158
  recurrence4A4_coeff_159
  recurrence4A4_coeff_16
  recurrence4A4_coeff_160
  recurrence4A4_coeff_161
  recurrence4A4_coeff_162
  recurrence4A4_coeff_163
  recurrence4A4_coeff_164
  recurrence4A4_coeff_165
  recurrence4A4_coeff_166
  recurrence4A4_coeff_167
  recurrence4A4_coeff_168
  recurrence4A4_coeff_169
  recurrence4A4_coeff_17
  recurrence4A4_coeff_170
  recurrence4A4_coeff_171
  recurrence4A4_coeff_172
  recurrence4A4_coeff_173
  recurrence4A4_coeff_174
  recurrence4A4_coeff_175
  recurrence4A4_coeff_176
  recurrence4A4_coeff_177
  recurrence4A4_coeff_178
  recurrence4A4_coeff_18
  recurrence4A4_coeff_19
  recurrence4A4_coeff_2
  recurrence4A4_coeff_20
  recurrence4A4_coeff_21
  recurrence4A4_coeff_22
  recurrence4A4_coeff_23
  recurrence4A4_coeff_24
  recurrence4A4_coeff_25
  recurrence4A4_coeff_26
  recurrence4A4_coeff_27
  recurrence4A4_coeff_28
  recurrence4A4_coeff_29
  recurrence4A4_coeff_3
  recurrence4A4_coeff_30
  recurrence4A4_coeff_31
  recurrence4A4_coeff_32
  recurrence4A4_coeff_33
  recurrence4A4_coeff_34
  recurrence4A4_coeff_35
  recurrence4A4_coeff_36
  recurrence4A4_coeff_37
  recurrence4A4_coeff_38
  recurrence4A4_coeff_39
  recurrence4A4_coeff_4
  recurrence4A4_coeff_40
  recurrence4A4_coeff_41
  recurrence4A4_coeff_42
  recurrence4A4_coeff_43
  recurrence4A4_coeff_44
  recurrence4A4_coeff_45
  recurrence4A4_coeff_46
  recurrence4A4_coeff_47
  recurrence4A4_coeff_48
  recurrence4A4_coeff_49
  recurrence4A4_coeff_5
  recurrence4A4_coeff_50
  recurrence4A4_coeff_51
  recurrence4A4_coeff_52

attribute [local simp]
  recurrence4A4_coeff_53
  recurrence4A4_coeff_54
  recurrence4A4_coeff_55
  recurrence4A4_coeff_56
  recurrence4A4_coeff_57
  recurrence4A4_coeff_58
  recurrence4A4_coeff_59
  recurrence4A4_coeff_6
  recurrence4A4_coeff_60
  recurrence4A4_coeff_61
  recurrence4A4_coeff_62
  recurrence4A4_coeff_63
  recurrence4A4_coeff_64
  recurrence4A4_coeff_65
  recurrence4A4_coeff_66
  recurrence4A4_coeff_67
  recurrence4A4_coeff_68
  recurrence4A4_coeff_69
  recurrence4A4_coeff_7
  recurrence4A4_coeff_70
  recurrence4A4_coeff_71
  recurrence4A4_coeff_72
  recurrence4A4_coeff_73
  recurrence4A4_coeff_74
  recurrence4A4_coeff_75
  recurrence4A4_coeff_76
  recurrence4A4_coeff_77
  recurrence4A4_coeff_78
  recurrence4A4_coeff_79
  recurrence4A4_coeff_8
  recurrence4A4_coeff_80
  recurrence4A4_coeff_81
  recurrence4A4_coeff_82
  recurrence4A4_coeff_83
  recurrence4A4_coeff_84
  recurrence4A4_coeff_85
  recurrence4A4_coeff_86
  recurrence4A4_coeff_87
  recurrence4A4_coeff_88
  recurrence4A4_coeff_89
  recurrence4A4_coeff_9
  recurrence4A4_coeff_90
  recurrence4A4_coeff_91
  recurrence4A4_coeff_92
  recurrence4A4_coeff_93
  recurrence4A4_coeff_94
  recurrence4A4_coeff_95
  recurrence4A4_coeff_96
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99
  recurrence4B2_coeff_0
  recurrence4B2_coeff_1
  recurrence4B2_coeff_10
  recurrence4B2_coeff_100
  recurrence4B2_coeff_101
  recurrence4B2_coeff_102
  recurrence4B2_coeff_103
  recurrence4B2_coeff_104
  recurrence4B2_coeff_105
  recurrence4B2_coeff_106
  recurrence4B2_coeff_107
  recurrence4B2_coeff_108
  recurrence4B2_coeff_109

attribute [local simp]
  recurrence4B2_coeff_11
  recurrence4B2_coeff_110
  recurrence4B2_coeff_111
  recurrence4B2_coeff_112
  recurrence4B2_coeff_113
  recurrence4B2_coeff_114
  recurrence4B2_coeff_115
  recurrence4B2_coeff_116
  recurrence4B2_coeff_117
  recurrence4B2_coeff_118
  recurrence4B2_coeff_119
  recurrence4B2_coeff_12
  recurrence4B2_coeff_120
  recurrence4B2_coeff_121
  recurrence4B2_coeff_122
  recurrence4B2_coeff_123
  recurrence4B2_coeff_124
  recurrence4B2_coeff_125
  recurrence4B2_coeff_126
  recurrence4B2_coeff_127
  recurrence4B2_coeff_128
  recurrence4B2_coeff_129
  recurrence4B2_coeff_13
  recurrence4B2_coeff_130
  recurrence4B2_coeff_131
  recurrence4B2_coeff_132
  recurrence4B2_coeff_133
  recurrence4B2_coeff_134
  recurrence4B2_coeff_135
  recurrence4B2_coeff_136
  recurrence4B2_coeff_137
  recurrence4B2_coeff_138
  recurrence4B2_coeff_139
  recurrence4B2_coeff_14
  recurrence4B2_coeff_140
  recurrence4B2_coeff_141
  recurrence4B2_coeff_142
  recurrence4B2_coeff_143
  recurrence4B2_coeff_144
  recurrence4B2_coeff_145
  recurrence4B2_coeff_146
  recurrence4B2_coeff_147
  recurrence4B2_coeff_148
  recurrence4B2_coeff_149
  recurrence4B2_coeff_15
  recurrence4B2_coeff_150
  recurrence4B2_coeff_151
  recurrence4B2_coeff_152
  recurrence4B2_coeff_153
  recurrence4B2_coeff_154
  recurrence4B2_coeff_155
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157
  recurrence4B2_coeff_158
  recurrence4B2_coeff_159
  recurrence4B2_coeff_16
  recurrence4B2_coeff_160
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167

attribute [local simp]
  recurrence4B2_coeff_168
  recurrence4B2_coeff_17
  recurrence4B2_coeff_18
  recurrence4B2_coeff_19
  recurrence4B2_coeff_2
  recurrence4B2_coeff_20
  recurrence4B2_coeff_21
  recurrence4B2_coeff_22
  recurrence4B2_coeff_23
  recurrence4B2_coeff_24
  recurrence4B2_coeff_25
  recurrence4B2_coeff_26
  recurrence4B2_coeff_27
  recurrence4B2_coeff_28
  recurrence4B2_coeff_29
  recurrence4B2_coeff_3
  recurrence4B2_coeff_30
  recurrence4B2_coeff_31
  recurrence4B2_coeff_32
  recurrence4B2_coeff_33
  recurrence4B2_coeff_34
  recurrence4B2_coeff_35
  recurrence4B2_coeff_36
  recurrence4B2_coeff_37
  recurrence4B2_coeff_38
  recurrence4B2_coeff_39
  recurrence4B2_coeff_4
  recurrence4B2_coeff_40
  recurrence4B2_coeff_41
  recurrence4B2_coeff_42
  recurrence4B2_coeff_43
  recurrence4B2_coeff_44
  recurrence4B2_coeff_45
  recurrence4B2_coeff_46
  recurrence4B2_coeff_47
  recurrence4B2_coeff_48
  recurrence4B2_coeff_49
  recurrence4B2_coeff_5
  recurrence4B2_coeff_50
  recurrence4B2_coeff_51
  recurrence4B2_coeff_52
  recurrence4B2_coeff_53
  recurrence4B2_coeff_54
  recurrence4B2_coeff_55
  recurrence4B2_coeff_56
  recurrence4B2_coeff_57
  recurrence4B2_coeff_58
  recurrence4B2_coeff_59
  recurrence4B2_coeff_6
  recurrence4B2_coeff_60
  recurrence4B2_coeff_61
  recurrence4B2_coeff_62
  recurrence4B2_coeff_63
  recurrence4B2_coeff_64
  recurrence4B2_coeff_65
  recurrence4B2_coeff_66
  recurrence4B2_coeff_67
  recurrence4B2_coeff_68
  recurrence4B2_coeff_69
  recurrence4B2_coeff_7
  recurrence4B2_coeff_70
  recurrence4B2_coeff_71
  recurrence4B2_coeff_72
  recurrence4B2_coeff_73

attribute [local simp]
  recurrence4B2_coeff_74
  recurrence4B2_coeff_75
  recurrence4B2_coeff_76
  recurrence4B2_coeff_77
  recurrence4B2_coeff_78
  recurrence4B2_coeff_79
  recurrence4B2_coeff_8
  recurrence4B2_coeff_80
  recurrence4B2_coeff_81
  recurrence4B2_coeff_82
  recurrence4B2_coeff_83
  recurrence4B2_coeff_84
  recurrence4B2_coeff_85
  recurrence4B2_coeff_86
  recurrence4B2_coeff_87
  recurrence4B2_coeff_88
  recurrence4B2_coeff_89
  recurrence4B2_coeff_9
  recurrence4B2_coeff_90
  recurrence4B2_coeff_91
  recurrence4B2_coeff_92
  recurrence4B2_coeff_93
  recurrence4B2_coeff_94
  recurrence4B2_coeff_95
  recurrence4B2_coeff_96
  recurrence4B2_coeff_97
  recurrence4B2_coeff_98
  recurrence4B2_coeff_99

theorem recurrence4B2A4_coeff_0 :
    recurrence4B2A4.coeff 0 =
      (-250723319715491387426816 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_1 :
    recurrence4B2A4.coeff 1 =
      (1864476666001642366720473472 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_2 :
    recurrence4B2A4.coeff 2 =
      (-3569686250833381937635207519792 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_3 :
    recurrence4B2A4.coeff 3 =
      (-537769351529052494138995328763480 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_4 :
    recurrence4B2A4.coeff 4 =
      (7110500776170259367016631016540540992 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_5 :
    recurrence4B2A4.coeff 5 =
      (-6255076918588020364139369479897699620168 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_6 :
    recurrence4B2A4.coeff 6 =
      (2426614741576056851443027134418781854258748 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_7 :
    recurrence4B2A4.coeff 7 =
      (-1429206354234730129809942456143335411719639650 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_8 :
    recurrence4B2A4.coeff 8 =
      (1108097447283585225396256906314174821245125269500 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_9 :
    recurrence4B2A4.coeff 9 =
      (-367284853420002635620590002294630101260396320550060 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_10 :
    recurrence4B2A4.coeff 10 =
      (-76101461934266160011199120718902905397684798944098844 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_11 :
    recurrence4B2A4.coeff 11 =
      (115047717663466810038290548993233867418835761025599185901 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_12 :
    recurrence4B2A4.coeff 12 =
      (-47935450340062161529473061999253649111401592517910788545441 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_13 :
    recurrence4B2A4.coeff 13 =
      (10858453469900909626777224769539580197096975507937383437871215 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_14 :
    recurrence4B2A4.coeff 14 =
      (-1309508251955955536567967993760896612998366449886922540725633641 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_15 :
    recurrence4B2A4.coeff 15 =
      (44593500571543711823180292973405911629003831366358303727936181411 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_16 :
    recurrence4B2A4.coeff 16 =
      (-7534778521895817897236503938612743142629432083149724370879903853430 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_17 :
    recurrence4B2A4.coeff 17 =
      ((1 * 10 ^ 70 +
        2931840542876155429120004319988556378002835211271618891098430103559398) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_18 :
    recurrence4B2A4.coeff 18 =
      -((620 * 10 ^ 70 +
        9868794591161146589212683876744790941595464994046548633450616915458329) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_19 :
    recurrence4B2A4.coeff 19 =
      ((190967 * 10 ^ 70 +
        3602457576660064891718325780827661561360025554877397162291124109938802) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_20 :
    recurrence4B2A4.coeff 20 =
      -((45245227 * 10 ^ 70 +
        9528046842746793724200036755756903260200582827460270210908364962513830) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_21 :
    recurrence4B2A4.coeff 21 =
      ((8798099602 * 10 ^ 70 +
        5108406791725778420033506901305377648246280487961495031340756493648127) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_22 :
    recurrence4B2A4.coeff 22 =
      -((1434363610433 * 10 ^ 70 +
        2818543423062394532265784381274917710717369779989952261798564181877401) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_23 :
    recurrence4B2A4.coeff 23 =
      ((196201738880345 * 10 ^ 70 +
        1336192959744305434260814260398491071502211239014964159580860025263713) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_24 :
    recurrence4B2A4.coeff 24 =
      -((22101978243623940 * 10 ^ 70 +
        3711239482417576976846035089494679750905368473545327617912561059765089) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_25 :
    recurrence4B2A4.coeff 25 =
      ((1930247162433618915 * 10 ^ 70 +
        8314899743149801209544888052664252079616528154124588988226503017556975) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_26 :
    recurrence4B2A4.coeff 26 =
      -((102273239584682030343 * 10 ^ 70 +
        7195562905365162254567820512604782165375282270746959264777161078576959) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_27 :
    recurrence4B2A4.coeff 27 =
      -((3688589242541473888897 * 10 ^ 70 +
        1521115112866276766230510926927930215332762426212443004414590823901956) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_28 :
    recurrence4B2A4.coeff 28 =
      ((1891438540485751878524048 * 10 ^ 70 +
        3841040467826977263095485383797140635580344346117786956155156351090480) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_29 :
    recurrence4B2A4.coeff 29 =
      -((313349742802975424412566826 * 10 ^ 70 +
        5052266482493022556497174788611252999561341378310728359995198466518984) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_30 :
    recurrence4B2A4.coeff 30 =
      ((38032869794394728502892794556 * 10 ^ 70 +
        6975228124433035109273209765377988395436469141799693136265136954738208) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_31 :
    recurrence4B2A4.coeff 31 =
      -((3830920177060954553472859923315 * 10 ^ 70 +
        7794589174345229489571445472556894822967480882174797929354313283342614) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_32 :
    recurrence4B2A4.coeff 32 =
      ((335176221239636550260582138982033 * 10 ^ 70 +
        1727915931643038232874671757414051397213510253447597153237390376838761) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_33 :
    recurrence4B2A4.coeff 33 =
      -((26058008456666328377531551198934977 * 10 ^ 70 +
        0835164172168132872890890642908370054662836022167422865620505311353128) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (33 - x)) = _
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_34 :
    recurrence4B2A4.coeff 34 =
      ((1824587931475987246517482406543829509 * 10 ^ 70 +
        7994913091345693882717777305698288162344742034477155457786326802923592) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (34 - x)) = _
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_35 :
    recurrence4B2A4.coeff 35 =
      -((116102061801450769327505534598369915275 * 10 ^ 70 +
        0160393736685144102695732050011053778497514264163413231166773176916325) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (35 - x)) = _
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_36 :
    recurrence4B2A4.coeff 36 =
      ((6757274863569242899901223575007104106778 * 10 ^ 70 +
        5230622578803450361782347149354198104192550192014982105598574798739403) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (36 - x)) = _
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_37 :
    recurrence4B2A4.coeff 37 =
      -((361489671500779623949241871901688374042645 * 10 ^ 70 +
        6145410294920790161926729669056394055882866240322836509084515797268299) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (37 - x)) = _
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_38 :
    recurrence4B2A4.coeff 38 =
      ((17844533077206598135177825280157258053272278 * 10 ^ 70 +
        3483975743737091277694042621958760853824071776665058027947686326364707) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (38 - x)) = _
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_39 :
    recurrence4B2A4.coeff 39 =
      -((815410192045601857329690609626624543107840079 * 10 ^ 70 +
        8019712882274404459773908056683748560621633364668792710951274233602165) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (39 - x)) = _
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_40 :
    recurrence4B2A4.coeff 40 =
      ((34581649834613834706154213513051833802143971029 * 10 ^ 70 +
        5563113758839669763298520363708457754078113652635150039840424841787369) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (40 - x)) = _
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_41 :
    recurrence4B2A4.coeff 41 =
      -((1364132481751366218506370342623966742910326419036 * 10 ^ 70 +
        8291666306375401926552837180754796646834310531483918748110440996728127) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (41 - x)) = _
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_42 :
    recurrence4B2A4.coeff 42 =
      ((50139786830717165234481993537192573756989000701755 * 10 ^ 70 +
        5860894219540593922520619996839864935027896252448285402810469921394168) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (42 - x)) = _
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_43 :
    recurrence4B2A4.coeff 43 =
      -((1719647366949173555922279131663302846703795437395982 * 10 ^ 70 +
        4983987955419099497562759137933392573998595502982875718367077614705412) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (43 - x)) = _
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_44 :
    recurrence4B2A4.coeff 44 =
      ((55091336076499940535950799302496406282350606211376243 * 10 ^ 70 +
        9644294987060014234873775479272338364575642808309506702176605917104766) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (44 - x)) = _
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_45 :
    recurrence4B2A4.coeff 45 =
      -((1649660615427960993619303902199393685729069414332227573 * 10 ^ 70 +
        8747759706679811943133505370081371223950080021271497264211201496268104) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (45 - x)) = _
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_46 :
    recurrence4B2A4.coeff 46 =
      ((46179005053010967834304794787679298949438002245064988646 * 10 ^ 70 +
        9016416409415359169806771390770323119107659940992196711236876348218261) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (46 - x)) = _
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_47 :
    recurrence4B2A4.coeff 47 =
      -((1207911579845617098914637267244582409496049161481667872149 * 10 ^ 70 +
        4374342295368943178675546006275406435068899767358999560911562941842509) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (47 - x)) = _
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_48 :
    recurrence4B2A4.coeff 48 =
      ((29484537361086172062840421545232316705368222161987518312081 * 10 ^ 70 +
        1355423591525122042763615180442712845628480206561065825956179119973403) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (48 - x)) = _
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_49 :
    recurrence4B2A4.coeff 49 =
      -((669870014335153566657956168284240777409960993473532198423506 * 10 ^ 70 +
        6063333155369493472770390065953224250478432166542600499302858905679164) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (49 - x)) = _
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_50 :
    recurrence4B2A4.coeff 50 =
      ((14098919823713827331988710677223377203117299548906422282473868 * 10 ^ 70 +
        1973779492114580918629666551409746811667774898516509446905508746702131) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (50 - x)) = _
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_51 :
    recurrence4B2A4.coeff 51 =
      -((272604275292922453663082550594846516807927406434222617201151446 * 10 ^ 70 +
        3822590635544137972083899571650446421306161679186412641456593497819466) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (51 - x)) = _
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_52 :
    recurrence4B2A4.coeff 52 =
      ((4766168366112645997205443657894495973700912195956391946132896020 * 10 ^ 70 +
        4347729252182763621677326644942180060006131899591051781131084212393418) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (52 - x)) = _
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_53 :
    recurrence4B2A4.coeff 53 =
      -((72886712770076133340003014788850916717279135419352349856251864661 * 10 ^ 70 +
        2118987223553884605049295444319971629531302428947011105568320096870936) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (53 - x)) = _
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_54 :
    recurrence4B2A4.coeff 54 =
      ((893089505348588657766325659890121999822154543174709813074933336751 * 10 ^ 70 +
        8016689219780435242003441578979125492930097816357185196442673382892139) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (54 - x)) = _
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_55 :
    recurrence4B2A4.coeff 55 =
      -((5828690320607545914677535266063768582473896497067574483122986275603 * 10 ^ 70 +
        7746714333571799355588583746839015181140182604099254919165873565518895) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (55 - x)) = _
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_56 :
    recurrence4B2A4.coeff 56 =
      -((106425874410547567304650137411090801444563854751198862184650292245516 * 10 ^ 70 +
        5110028472345523895626313505246741239210441893484787219002717148378069) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (56 - x)) = _
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_57 :
    recurrence4B2A4.coeff 57 =
      ((5708569714897884256299516041182764067178085663130427592888206656298262 * 10 ^ 70 +
        3513512808601089405251757600983516551823478636807400288929491796431564) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (57 - x)) = _
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_58 :
    recurrence4B2A4.coeff 58 =
      -(((16 * 10 ^ 70 +
        1994504717074827271462534044768612069529663717476117641010654170573510) * 10 ^ 70 +
        6276699437428076407249898224800140273971565628714718474931406145081317) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (58 - x)) = _
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_59 :
    recurrence4B2A4.coeff 59 =
      (((369 * 10 ^ 70 +
        5633506073163803676718282519122429518213570295214890863417699624546177) * 10 ^ 70 +
        5074755132377149557041531043250438331773798658922901963900415499233597) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (59 - x)) = _
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_60 :
    recurrence4B2A4.coeff 60 =
      -(((7419 * 10 ^ 70 +
        7519711765764923126345049743407058146979415249648197750135159930836115) * 10 ^ 70 +
        6932711319130301025848793265419770674029535649596390347073874921039908) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (60 - x)) = _
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_61 :
    recurrence4B2A4.coeff 61 =
      (((135828 * 10 ^ 70 +
        7671902381270864032731431903200379440119805001512413390216372235900877) * 10 ^ 70 +
        4168623702866525572379980249394289502711242694795862975163822650999967) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (61 - x)) = _
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_62 :
    recurrence4B2A4.coeff 62 =
      -(((2308050 * 10 ^ 70 +
        0662480434515538789246702155289011672666772591236862411492479517110010) * 10 ^ 70 +
        4504677357643485408857640411590143111872940394362670942626164767307070) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (62 - x)) = _
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_63 :
    recurrence4B2A4.coeff 63 =
      (((36785580 * 10 ^ 70 +
        4349568630241084851922562399393573092690351461140052215447752900106597) * 10 ^ 70 +
        4662668467213260964346459481174920843779578550460371510767195524022877) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (63 - x)) = _
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_64 :
    recurrence4B2A4.coeff 64 =
      -(((553625837 * 10 ^ 70 +
        8360501959337681302300643535554662918077134541495389771715425595986773) * 10 ^ 70 +
        4992233518233178308542219230543567461106493620523313230067471577287040) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (64 - x)) = _
  rw [show 65 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_65 :
    recurrence4B2A4.coeff 65 =
      (((7904974074 * 10 ^ 70 +
        0964546665283683188732163082323760947761069811261248134916837779493451) * 10 ^ 70 +
        1022759438784291319100638705703176855901438041068103478385190998093450) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (65 - x)) = _
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
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_66 :
    recurrence4B2A4.coeff 66 =
      -(((107456843140 * 10 ^ 70 +
        0556136117300599481187102325600155384359646889737839053763991178052105) * 10 ^ 70 +
        0312327671194276085501621521062868803987341306520912435718452870910981) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (66 - x)) = _
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
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_67 :
    recurrence4B2A4.coeff 67 =
      (((1394372005831 * 10 ^ 70 +
        4082666125214609263660323752911435137227605807213578776393480303040290) * 10 ^ 70 +
        1612307059069892357332798211045881066752638638530201015218108020731695) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (67 - x)) = _
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
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_68 :
    recurrence4B2A4.coeff 68 =
      -(((17308709769958 * 10 ^ 70 +
        7692866883299494855826369592823454464770061350104636929468782778502280) * 10 ^ 70 +
        0388223011189122907651381165934667602346124092745199503506075915040067) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (68 - x)) = _
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
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_69 :
    recurrence4B2A4.coeff 69 =
      (((205902016343702 * 10 ^ 70 +
        7650230867409491377250231769963215465157414751158486660213220538292198) * 10 ^ 70 +
        9856422267573584254178708381785651204228931057466777851484794542360526) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (69 - x)) = _
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
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_70 :
    recurrence4B2A4.coeff 70 =
      -(((2350806667332144 * 10 ^ 70 +
        5386899012672728179797678654354346031411431433887077745997638937039111) * 10 ^ 70 +
        3404082349303508975178160190709550408302591410059350716326796704817494) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (70 - x)) = _
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_71 :
    recurrence4B2A4.coeff 71 =
      (((25792646363158258 * 10 ^ 70 +
        9563692466845701423667441986563663359133529633679905903663779080522575) * 10 ^ 70 +
        9957266402841415700685943833124440304897401809174642977972954383930871) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (71 - x)) = _
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
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_72 :
    recurrence4B2A4.coeff 72 =
      -(((272265083576200837 * 10 ^ 70 +
        7912560667062170154675260078742605353202976916415067637399131038673515) * 10 ^ 70 +
        7163017954831796916655058883085764230401238378193010709722698154424443) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (72 - x)) = _
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
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_73 :
    recurrence4B2A4.coeff 73 =
      (((2767872038985009830 * 10 ^ 70 +
        4656710763651960833072072116349000464629908424209655691127449917119848) * 10 ^ 70 +
        1307736443296969719590827603681601349951569560503512976719464508459061) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (73 - x)) = _
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
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_74 :
    recurrence4B2A4.coeff 74 =
      -(((27124149245619473066 * 10 ^ 70 +
        5508554981453099885525952592300973626456479099952754603895257989918594) * 10 ^ 70 +
        5566021405973902436832103895328699173931516561871458811152345982051885) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (74 - x)) = _
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
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_75 :
    recurrence4B2A4.coeff 75 =
      (((256439680535666165277 * 10 ^ 70 +
        9971029767839823482325081965345068449793066338935490014821968305228690) * 10 ^ 70 +
        6283700213914539795680432615687752779690872683724674939162573669754657) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (75 - x)) = _
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_76 :
    recurrence4B2A4.coeff 76 =
      -(((2340814635344036785646 * 10 ^ 70 +
        0172410479872762032857829831702901103940128886381690682205705986042241) * 10 ^ 70 +
        7996346468976650616805902817040725392412593534714212090088688238847599) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (76 - x)) = _
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_77 :
    recurrence4B2A4.coeff 77 =
      (((20644793774088341209445 * 10 ^ 70 +
        8796744516896506333576965166203468672741814183479815918048861147498410) * 10 ^ 70 +
        4833526728338318585475985465867371374784987499523109582760421185827664) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (77 - x)) = _
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_78 :
    recurrence4B2A4.coeff 78 =
      -(((176036897693003460181251 * 10 ^ 70 +
        3549906173519214618253864615327799991112186315364021928958523462621464) * 10 ^ 70 +
        4795853324539117715654393315411936243295360039782589946767074716035300) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (78 - x)) = _
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

theorem recurrence4B2A4_coeff_79 :
    recurrence4B2A4.coeff 79 =
      (((1452165406992312482326819 * 10 ^ 70 +
        9619556078438448622451093139183947194458234997794856189007821007250385) * 10 ^ 70 +
        5336911156213634133574417501910386806803765542697139387218379308835240) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (79 - x)) = _
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
