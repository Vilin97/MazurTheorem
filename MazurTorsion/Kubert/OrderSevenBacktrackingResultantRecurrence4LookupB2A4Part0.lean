/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B2A4 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_80 :
    recurrence4B2A4.coeff 80 =
      -(((11595813669254907990391103 * 10 ^ 70 +
        0456532632151848404415061490340078865213493247761621124537469510599441) * 10 ^ 70 +
        4113248103784603370838662240550125997200227428421225012023570637304960) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (80 - x)) = _
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_81 :
    recurrence4B2A4.coeff 81 =
      (((89680589222394813667384957 * 10 ^ 70 +
        0462041979638923477764219578328834592016308338018553914890879057851832) * 10 ^ 70 +
        6738474262852694041643540845856555691351847970352035024131471416984100) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (81 - x)) = _
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_82 :
    recurrence4B2A4.coeff 82 =
      -(((672100752757734898443691528 * 10 ^ 70 +
        9272498154876085723681960714761767776141550103653626140739953966338707) * 10 ^ 70 +
        2308841791433446676271550009230768405735633548477143668701759851884844) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (82 - x)) = _
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_83 :
    recurrence4B2A4.coeff 83 =
      (((4883421247852366635235182233 * 10 ^ 70 +
        8001439304152398984540995525742063786712412336846838940976022133150807) * 10 ^ 70 +
        3300966247490344054967606353347363109589179406042156242209623168772628) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (83 - x)) = _
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_84 :
    recurrence4B2A4.coeff 84 =
      -(((34416971701283188073740791155 * 10 ^ 70 +
        1444027034977854007310281583095698177153270554197059913489331215180546) * 10 ^ 70 +
        8299690366932970313752806891897776516831421791258816654675047243635532) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (84 - x)) = _
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_85 :
    recurrence4B2A4.coeff 85 =
      (((235382983135447263575692720865 * 10 ^ 70 +
        8465678747318728848886066964145936109995022564276134614474203250253305) * 10 ^ 70 +
        4397762179581395328524325812758599047386134797899753962190231856591770) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (85 - x)) = _
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_86 :
    recurrence4B2A4.coeff 86 =
      -(((1562852373869783278175212272095 * 10 ^ 70 +
        4957373741974926830213466699423921352616132141600387526105019989128996) * 10 ^ 70 +
        9368835941412752839369093968795637864061122081164347673703232734576517) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (86 - x)) = _
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_87 :
    recurrence4B2A4.coeff 87 =
      (((10078126397369841109344450433352 * 10 ^ 70 +
        5653924308142869433373927173068613995730897558435066869864144779234389) * 10 ^ 70 +
        3671896388289419835465848101940736246840218940026077071763184441420354) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (87 - x)) = _
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_88 :
    recurrence4B2A4.coeff 88 =
      -(((63143921076866472721702817541578 * 10 ^ 70 +
        2582451804073015106208156285386898334500259528295882660981388293863467) * 10 ^ 70 +
        8913267407521628621623197320118552093236432513969806533963536949313023) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (88 - x)) = _
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_89 :
    recurrence4B2A4.coeff 89 =
      (((384536113905335095092376306403400 * 10 ^ 70 +
        0442782324436964589916064790782983747906129006781147535735826768918896) * 10 ^ 70 +
        3537089408995592392869611196954339292802716019561110012437752050496375) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (89 - x)) = _
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_90 :
    recurrence4B2A4.coeff 90 =
      -(((2276952237642470422411346986817856 * 10 ^ 70 +
        2382119671564835552419647845640901342432749799508721690847642314955432) * 10 ^ 70 +
        2292047415320010197929457836344729511048267958268937478621614876556446) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (90 - x)) = _
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_91 :
    recurrence4B2A4.coeff 91 =
      (((13113936707721774573965608481803112 * 10 ^ 70 +
        6097952317349004841308867675215040975570187829202092019612304958887334) * 10 ^ 70 +
        0422999364875755155807717965530056082293693836684980718676539356524445) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (91 - x)) = _
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_92 :
    recurrence4B2A4.coeff 92 =
      -(((73488596087511574064520623180166642 * 10 ^ 70 +
        3917823577297824409478332417300736952125388782629308791855384581409789) * 10 ^ 70 +
        3132239964203641902590336746890734955682452519941458450197057038950378) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (92 - x)) = _
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_93 :
    recurrence4B2A4.coeff 93 =
      (((400824556005233075228375164908308545 * 10 ^ 70 +
        3146785009038297461363627224576948313642262715169643982380722236408806) * 10 ^ 70 +
        7599590295638052114395445183529412804069134142724686240513748017531331) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (93 - x)) = _
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_94 :
    recurrence4B2A4.coeff 94 =
      -(((2128485688777040388785640717012481574 * 10 ^ 70 +
        0280807182756460695688483471500689017831081720976869648806508077219431) * 10 ^ 70 +
        8058698919618385800370241077871428938869369908698290551417592913538363) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (94 - x)) = _
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_95 :
    recurrence4B2A4.coeff 95 =
      (((11007754519988446161001979585719411061 * 10 ^ 70 +
        6825419742517843600521208803139600098702864571224132135731887817286388) * 10 ^ 70 +
        2058741170314772421688739655545207989392838949424346246576400458000882) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (95 - x)) = _
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_96 :
    recurrence4B2A4.coeff 96 =
      -(((55457858697287026150491101106594925600 * 10 ^ 70 +
        5663067455941658216501229727069030547257386725464975795988142477327829) * 10 ^ 70 +
        9040812472837039073311475981728546816321138517806276789070506976285975) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (96 - x)) = _
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
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_97 :
    recurrence4B2A4.coeff 97 =
      (((272260119467712559647646926105449446994 * 10 ^ 70 +
        8179487131924656366855212795203633026884979303987594530115622629898723) * 10 ^ 70 +
        5377684580194052471494992183991933477682581585868809098445556841323329) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (97 - x)) = _
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
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_98 :
    recurrence4B2A4.coeff 98 =
      -(((1302798910748048257249502029936117475898 * 10 ^ 70 +
        5326226846282407908946694700334485752009831214809671652410251199451788) * 10 ^ 70 +
        4843569746309905327816677340591224145914395384949537896253944046010872) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (98 - x)) = _
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
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_99 :
    recurrence4B2A4.coeff 99 =
      (((6077917901602200379887110593260115129807 * 10 ^ 70 +
        0845655538627620314275234449219729741859595604960063604008413158267418) * 10 ^ 70 +
        5549162628385406206621597282091423355812048093575959383127494475873108) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (99 - x)) = _
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
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_100 :
    recurrence4B2A4.coeff 100 =
      -(((27651838097113837726316769631547898997341 * 10 ^ 70 +
        4954959290424553812232691317380808086449239519760215972812831695184657) * 10 ^ 70 +
        1877211154581738976157028732217640000673886528873634714976271635140930) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (100 - x)) = _
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
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_101 :
    recurrence4B2A4.coeff 101 =
      (((122712470179776835558664845086906244022429 * 10 ^ 70 +
        3228384543287757866999337625240799271621356984241980124644397126657431) * 10 ^ 70 +
        9603286591260441840005844360302379567476152058907500321211754506252247) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (101 - x)) = _
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
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_102 :
    recurrence4B2A4.coeff 102 =
      -(((531311205284340983013740204786521441324699 * 10 ^ 70 +
        5352771246618325139594920446469803502403346182060114770949589272627586) * 10 ^ 70 +
        2264008300178203279244520642560820085724253536539691667287288296754683) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (102 - x)) = _
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_103 :
    recurrence4B2A4.coeff 103 =
      (((2244922336447808535971289213653334191475701 * 10 ^ 70 +
        5981024965088567889495969773107121844052119420399475588310515881291633) * 10 ^ 70 +
        4586989017192813149303850139676448037537072930579132573435243783339357) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (103 - x)) = _
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
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_104 :
    recurrence4B2A4.coeff 104 =
      -(((9258460298553203067939562223076771040010490 * 10 ^ 70 +
        0579863033419938025475100553378483877063764337783101620846682516150246) * 10 ^ 70 +
        3961353931165543764143495290677659255685079262156418193955262476197904) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (104 - x)) = _
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
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_105 :
    recurrence4B2A4.coeff 105 =
      (((37277863894209888797088054596738878372934449 * 10 ^ 70 +
        7711555941524696077784391211217368803750301091204586699019224720792160) * 10 ^ 70 +
        6938533327027379523797669079007834746629369871832998467268432986503654) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (105 - x)) = _
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
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_106 :
    recurrence4B2A4.coeff 106 =
      -(((146563069994805839463091822522725569285035668 * 10 ^ 70 +
        5153659656927210402055970345254253881256490566543507776667403116573430) * 10 ^ 70 +
        3034633344479929240749990436610106351407136537217840323587410889385351) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (106 - x)) = _
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
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_107 :
    recurrence4B2A4.coeff 107 =
      (((562785303497307149325327924216229441541489006 * 10 ^ 70 +
        3754139898689605321547274368524994409626192744396608691955144326792038) * 10 ^ 70 +
        1479752903956785340488664427633703545718765009844755166885662601592440) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (107 - x)) = _
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_108 :
    recurrence4B2A4.coeff 108 =
      -(((2110988995783254204239682397685688963925885550 * 10 ^ 70 +
        8870629048705683898747915545423151650562205772340341426550923109634473) * 10 ^ 70 +
        4570457500396995825064690303619179935014508864814724105730327994211786) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (108 - x)) = _
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_109 :
    recurrence4B2A4.coeff 109 =
      (((7736271057669275622377156726662520320330754224 * 10 ^ 70 +
        5176114344080457130072703267956787713729568026825726571866879456065111) * 10 ^ 70 +
        8370333158010838377961941793030375779619700474714390903724212365814945) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (109 - x)) = _
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_110 :
    recurrence4B2A4.coeff 110 =
      -(((27704767982805084940500312600654597203078495801 * 10 ^ 70 +
        9794616728460827010690677457113809504277706831272501487387575870845267) * 10 ^ 70 +
        2197077654092936857897967201681097084637084001532208468054519442414496) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (110 - x)) = _
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_111 :
    recurrence4B2A4.coeff 111 =
      (((96967546296380296022336128283507520121697153419 * 10 ^ 70 +
        7761128597640840299034502557943046946727013007765537986077885523895789) * 10 ^ 70 +
        2116572305181521456496854179054793756175072432814749150643651528550299) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (111 - x)) = _
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_112 :
    recurrence4B2A4.coeff 112 =
      -(((331754345256507927735212689701942800889452408796 * 10 ^ 70 +
        2749391866477599910752704250208111370899541857768624150838659064232492) * 10 ^ 70 +
        2650833107232599562312675193122710930306701218626630919450333060338940) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (112 - x)) = _
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_113 :
    recurrence4B2A4.coeff 113 =
      (((1109664960572335344757198906039817850655379847876 * 10 ^ 70 +
        8042288458450581494003166738357875035626700919775772823639775297285016) * 10 ^ 70 +
        1025143329146841935584383487349101834410691829395127696022336368146230) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (113 - x)) = _
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_114 :
    recurrence4B2A4.coeff 114 =
      -(((3629245891590410556833081168242864337736983370315 * 10 ^ 70 +
        1194402138323712197732441116209357058445902988806725122715669009212862) * 10 ^ 70 +
        7178600459343400619519566010843490105363217114299380414965644105704198) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (114 - x)) = _
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_115 :
    recurrence4B2A4.coeff 115 =
      (((11607855691753436801982644418715263795120553156022 * 10 ^ 70 +
        1674783379691217979674259119660173348003807709603005763198860513436456) * 10 ^ 70 +
        5409662217519610313649157417524593896405820553365834073436203549586415) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (115 - x)) = _
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_116 :
    recurrence4B2A4.coeff 116 =
      -(((36312668604055817308806784868238169578999168181546 * 10 ^ 70 +
        1675782106153183134221640868764222087535798494794658898880364602910426) * 10 ^ 70 +
        9421518892801482582275763088057169439299167440430928649304002663480996) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (116 - x)) = _
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_117 :
    recurrence4B2A4.coeff 117 =
      (((111119963077361312714433872135658667954296048788178 * 10 ^ 70 +
        0924275703323262420576376688104406925015413676713350594023468654384164) * 10 ^ 70 +
        2389137016961179104085376699768306256174172842698137378973182681857717) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (117 - x)) = _
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_118 :
    recurrence4B2A4.coeff 118 =
      -(((332666254831862142027006464500962894631108493724339 * 10 ^ 70 +
        6628143316230972367501494352392443166510216630232667037992698004234589) * 10 ^ 70 +
        2314280762196199195981149199361838310506583853623681360459425574755895) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (118 - x)) = _
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_119 :
    recurrence4B2A4.coeff 119 =
      (((974453171827600616355168668146122851437248858261833 * 10 ^ 70 +
        7324079588684083156534133483046761527880861966379263777714195889978526) * 10 ^ 70 +
        6470691159639145862567716172677133606011891063506660956578942474466907) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (119 - x)) = _
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_120 :
    recurrence4B2A4.coeff 120 =
      -(((2793183626243185299239526780905386842740271530540567 * 10 ^ 70 +
        8194455113634417923113499738808402516778157997488987269163790905241875) * 10 ^ 70 +
        4796524239052515779595781980025070316274860969533268739077244738975001) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (120 - x)) = _
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_121 :
    recurrence4B2A4.coeff 121 =
      (((7835612804914558049250458080625665589460077175083174 * 10 ^ 70 +
        7726872584235319564302491289535513866378264106517993906845393536664471) * 10 ^ 70 +
        3217856454825219478040990891567535110310344814725027436163048468802096) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (121 - x)) = _
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_122 :
    recurrence4B2A4.coeff 122 =
      -(((21514343053274948274936433638345325064670595117697873 * 10 ^ 70 +
        9120392747665873749249113304429394618795995672792298545946941216424586) * 10 ^ 70 +
        9301093987604033131398224700114299376767488540523961476752525671279393) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (122 - x)) = _
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_123 :
    recurrence4B2A4.coeff 123 =
      (((57824192312604711726152763015732927865422756141339140 * 10 ^ 70 +
        1561870658932996804725508348297287035048384297211086878451923919147608) * 10 ^ 70 +
        9717064477805705503769447382315290043527063715219117008313887592043020) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (123 - x)) = _
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_124 :
    recurrence4B2A4.coeff 124 =
      -(((152145893084213157011503993209269783012921817796866858 * 10 ^ 70 +
        6399077583369241892450551965750527761625869376045714202167466295896106) * 10 ^ 70 +
        9696552905453957165375123327478879828301276752466280349456930487415565) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (124 - x)) = _
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_125 :
    recurrence4B2A4.coeff 125 =
      (((391941273140756470108421498716710072360039355682504468 * 10 ^ 70 +
        2286794705328151465077819913570562886491546920898173788186448520667534) * 10 ^ 70 +
        5685199801670430228096771093291076598903926519943231815466954883583972) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (125 - x)) = _
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_126 :
    recurrence4B2A4.coeff 126 =
      -(((988623580608245774972938571493280955142807813967963181 * 10 ^ 70 +
        1589619626477040268958715785071372248483427667415735149482147897056776) * 10 ^ 70 +
        8918510405423539891656805123593104544815820140055714881119538730690640) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (126 - x)) = _
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_127 :
    recurrence4B2A4.coeff 127 =
      (((2441897428351316124983224542046332457621363795125713914 * 10 ^ 70 +
        9617566440036499112813263877225469720722355495967477832523949082403124) * 10 ^ 70 +
        3300830240869159217868545521333930436558949935482340564461074291278118) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (127 - x)) = _
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_128 :
    recurrence4B2A4.coeff 128 =
      -(((5906712884886334491193705365538821782678910182590165979 * 10 ^ 70 +
        0637663571340818717637997356340496212495424131783293397542606979749581) * 10 ^ 70 +
        6181012289954659101463045133321550130607224007355408139721833863309544) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (128 - x)) = _
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
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_129 :
    recurrence4B2A4.coeff 129 =
      (((13993296719803718406657867369977375607335957871848684833 * 10 ^ 70 +
        7371108831136272363817194143503987152140715617036870542684173505285251) * 10 ^ 70 +
        0936509295687872853562654010284018928201058649646667969476983509473934) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (129 - x)) = _
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
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_130 :
    recurrence4B2A4.coeff 130 =
      -(((32469976486580313952080023365728406089643667206192895745 * 10 ^ 70 +
        7970999082190378673759230533445384259164364494796823094514744123710068) * 10 ^ 70 +
        5166175678829384199881051820405027114480204945095284174095430144546675) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (130 - x)) = _
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
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_131 :
    recurrence4B2A4.coeff 131 =
      (((73800948388892663071660758299241837918814323519110237125 * 10 ^ 70 +
        3716877019005568467251067701364906366026935807664877824962382710982733) * 10 ^ 70 +
        5928177122155870039032430462943138970178984909016648783593437833449784) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (131 - x)) = _
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
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_132 :
    recurrence4B2A4.coeff 132 =
      -(((164319282027761018772309195724599024655931238260907268835 * 10 ^ 70 +
        8371733208342669557373360007061645468803921090987806036364514498859953) * 10 ^ 70 +
        6489382815164953480055948154460829410984509961221922251232509420265876) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (132 - x)) = _
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
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_133 :
    recurrence4B2A4.coeff 133 =
      (((358417006976306453943233077433937817669609221511902245436 * 10 ^ 70 +
        5650499406559945186857854539156879200490532235164663221033501566954461) * 10 ^ 70 +
        3819259271381911821459007331259255588192105680324973248245944117619344) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (133 - x)) = _
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
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_134 :
    recurrence4B2A4.coeff 134 =
      -(((765926967996451260170370105283204645315728769199108342716 * 10 ^ 70 +
        1703559660201876439829320559156372128828808932496347069924410282741603) * 10 ^ 70 +
        4654645453837630968721434339006478309617766220479555799068784098757366) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (134 - x)) = _
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_135 :
    recurrence4B2A4.coeff 135 =
      (((1603645099879294625403761241499243301215578262427311231919 * 10 ^ 70 +
        6690185323762160886652055207595327888807393239084464473638440141106268) * 10 ^ 70 +
        6792713485734486946468403400350842122401973370650179302265286332104446) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (135 - x)) = _
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
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_136 :
    recurrence4B2A4.coeff 136 =
      -(((3289827125658460716606535974969452550792597395392708581897 * 10 ^ 70 +
        9716947940017663456044863254786846342010918213136833476484704445463099) * 10 ^ 70 +
        1905179964630428763081241704386074637169104159842560029216743837574886) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (136 - x)) = _
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
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_137 :
    recurrence4B2A4.coeff 137 =
      (((6613050708991292749284004609047612602350268810070993467101 * 10 ^ 70 +
        9178927280594422025852124405596709901273810763916367946639935075983080) * 10 ^ 70 +
        8987080209853844543420114011273715342507473647627479791037121777479782) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (137 - x)) = _
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
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_138 :
    recurrence4B2A4.coeff 138 =
      -(((13026054546689201891552793001700692755209105289833625518729 * 10 ^ 70 +
        4610006438916100854142838299819785839471850543149977779450612745165085) * 10 ^ 70 +
        0356953000035362229650964097545166325205862316959011563899406403418716) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (138 - x)) = _
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
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_139 :
    recurrence4B2A4.coeff 139 =
      (((25143326365376079373133083652924286566644547333640069213531 * 10 ^ 70 +
        5997789601324738869118282014380627311911911931452675005586935229609007) * 10 ^ 70 +
        5247585992260720748081659815886978770398366805965568649532931341556150) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (139 - x)) = _
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_140 :
    recurrence4B2A4.coeff 140 =
      -(((47560466995939877669627706875651350395941879171212515012521 * 10 ^ 70 +
        9562730225131497568338422600165489972593452508389697099785116760157999) * 10 ^ 70 +
        7054625170795351126159715137750010009140536018441702933651416184711114) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (140 - x)) = _
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_141 :
    recurrence4B2A4.coeff 141 =
      (((88164941019430185844945323950269775091737885238863153358648 * 10 ^ 70 +
        3902925381739374818210348153000025936389359126172436130474984903782726) * 10 ^ 70 +
        0399514691572935273509675677592318317109543333590242166063704362408468) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (141 - x)) = _
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_142 :
    recurrence4B2A4.coeff 142 =
      -(((160170735789727240422378467502911117843047321657103809224233 * 10 ^ 70 +
        8699929831500696969853063355481485609715800258468886301333911383042990) * 10 ^ 70 +
        2321230435034409499507056908795524999718403585227537526797766312746713) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (142 - x)) = _
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_143 :
    recurrence4B2A4.coeff 143 =
      (((285178586702033509980197562949148841200435360123118517246668 * 10 ^ 70 +
        6025564667315682937865906881230490950368006891190831097500141135354066) * 10 ^ 70 +
        0205308030943432161978906936990991437333949614529561686540619742527055) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (143 - x)) = _
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_144 :
    recurrence4B2A4.coeff 144 =
      -(((497627278010161700922659460322267614193840093635205077969138 * 10 ^ 70 +
        1501786869150737832526782077612037503681320473255920666593670931574035) * 10 ^ 70 +
        9598776070769253599506793549212640859324531845490770665006047073066010) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (144 - x)) = _
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_145 :
    recurrence4B2A4.coeff 145 =
      (((851039848533294426330675292399530811144880529556322250042016 * 10 ^ 70 +
        1027977553426737783262041827745557033654799005956585132569887351360211) * 10 ^ 70 +
        2308505189704012921551902001638191045377835662727824269276353418144187) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (145 - x)) = _
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_146 :
    recurrence4B2A4.coeff 146 =
      -(((1426450761250305675407924058605105841847248835705755984822100 * 10 ^ 70 +
        1563565969250746138171406872047789289311479108256254670011812970125777) * 10 ^ 70 +
        8798767958202295374056571406791439097964246670757789153431250611484133) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (146 - x)) = _
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_147 :
    recurrence4B2A4.coeff 147 =
      (((2343285737022045514166672683945430000702097105618734182202273 * 10 ^ 70 +
        7322933102623084638266277690318410377480965673728346624073109346188444) * 10 ^ 70 +
        2696594357847158096910492874292841634859578724428083098990579688431901) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (147 - x)) = _
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_148 :
    recurrence4B2A4.coeff 148 =
      -(((3772708369956303675317507232269020336278330474185301859960923 * 10 ^ 70 +
        2838592230007803997697273042811918425105551415581868625629462005990320) * 10 ^ 70 +
        8960100502784126973482778154377521248871649545120090238287247998437894) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (148 - x)) = _
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_149 :
    recurrence4B2A4.coeff 149 =
      (((5953002725156784054194142780133308905527238983446138543405913 * 10 ^ 70 +
        0491506324085862318251835129897854442297354190763758003126603320457233) * 10 ^ 70 +
        1658564294198052854290298296685034384613951317952786290953469251681144) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (149 - x)) = _
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_150 :
    recurrence4B2A4.coeff 150 =
      -(((9205901608195178835581567749136244280566848933439600303642774 * 10 ^ 70 +
        9046967215191629402059059990130986967517172995750177208464543012648796) * 10 ^ 70 +
        3961629790126811705760581586490325531229112575002638090161610341597782) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (150 - x)) = _
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_151 :
    recurrence4B2A4.coeff 151 =
      (((13951905048524574240479570903906414735879903095300520089999072 * 10 ^ 70 +
        8996164497223857734268586587416359789771461077846010092278990069108075) * 10 ^ 70 +
        0540623261765501158727337601215636347587445072044759696938381014754203) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (151 - x)) = _
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_152 :
    recurrence4B2A4.coeff 152 =
      -(((20721629529940121025298832012816615347926792826056688173938705 * 10 ^ 70 +
        5898354736302834800903254256307344453179900344065327668950851358824925) * 10 ^ 70 +
        8587832852990059065801756637930538341181304868296696892335316496324530) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (152 - x)) = _
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_153 :
    recurrence4B2A4.coeff 153 =
      (((30159228537432348139858670871019634871320970383381839947960677 * 10 ^ 70 +
        6540459079571930176559088258433858320209659157687282340282833307383721) * 10 ^ 70 +
        4288295466328381395677988584849635963080946859840423122510385869809377) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (153 - x)) = _
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_154 :
    recurrence4B2A4.coeff 154 =
      -(((43013155225622266392021337867178541951306258308381604848732714 * 10 ^ 70 +
        3705429798998618719341578928436103623388724464924915044928411666112165) * 10 ^ 70 +
        3465119931478399431330389026264054997111052683594111763751032373733172) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (154 - x)) = _
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_155 :
    recurrence4B2A4.coeff 155 =
      (((60109294760996304980989818254405032387628381837193479259705195 * 10 ^ 70 +
        0736573340574946432062593964150860448805199178494105625605571584372855) * 10 ^ 70 +
        1746207234186098757184441960988896049485801548017319865910010282592186) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (155 - x)) = _
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_156 :
    recurrence4B2A4.coeff 156 =
      -(((82302102861430699006081078648452958633182422690293791803186356 * 10 ^ 70 +
        6676597264221156335747193601544652077736197693490334230376878645517071) * 10 ^ 70 +
        1013426748671526185607013700365561331564185306753955560534988065672458) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (156 - x)) = _
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_157 :
    recurrence4B2A4.coeff 157 =
      (((110401132554371337153730185680700375947114842405683820635377121 * 10 ^ 70 +
        5651622911184726308513356841584488054353586603702464629267650116023838) * 10 ^ 70 +
        8617662982362189277376271514864014099948336142054750493230309753383093) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (157 - x)) = _
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_158 :
    recurrence4B2A4.coeff 158 =
      -(((145073361501515670892361714204087618224184851799045697465733878 * 10 ^ 70 +
        6329124877852822464424398454352337815108704291104932932956060196739515) * 10 ^ 70 +
        3002035092914804835124570265287524719722286116233696143015316564855071) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (158 - x)) = _
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_159 :
    recurrence4B2A4.coeff 159 =
      (((186725958534951244343967214734610509381150448563787123476767083 * 10 ^ 70 +
        6896201313013864074479630754344369484425448387396588682319490062869253) * 10 ^ 70 +
        1354249110005469263113572414565827884927427152124867382094005624196494) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (159 - x)) = _
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_160 :
    recurrence4B2A4.coeff 160 =
      -(((235379144060368009688360029379838234420351633908820113998627991 * 10 ^ 70 +
        3417379885386668200853658104508398782355204205913094488872256169193464) * 10 ^ 70 +
        5283855908321870067206039983780258644571413075865120328631527985145243) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (160 - x)) = _
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
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_161 :
    recurrence4B2A4.coeff 161 =
      (((290543854794216278047215969986385048854138075826594542827867948 * 10 ^ 70 +
        8775535827494131042083368783672221246315779014347326883210761693463385) * 10 ^ 70 +
        9918545837663643460775001169336990406229428326429355043969543803063257) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (161 - x)) = _
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
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_162 :
    recurrence4B2A4.coeff 162 =
      -(((351122982871747124586778520294796489612423265098884664379243970 * 10 ^ 70 +
        9955451758501871807074143941039843428882218154529478146679082816792357) * 10 ^ 70 +
        6910451823471141354012817489304217481526207547125000356119251719840944) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (162 - x)) = _
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
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_163 :
    recurrence4B2A4.coeff 163 =
      (((415356857001269507943319008516943295121443342536189294858030042 * 10 ^ 70 +
        4416391861482697275401507071164372623640571478309482943145363714261467) * 10 ^ 70 +
        1794213943747355315680038773524508488569831386035262497691426011693922) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (163 - x)) = _
  rw [show 164 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_164 :
    recurrence4B2A4.coeff 164 =
      -(((480832319020258227632242316525812416987897688724429940201105021 * 10 ^ 70 +
        8420546782301986367340174583007741369671324574720678501110024307871915) * 10 ^ 70 +
        5068875719386612557745161012628895035252729344676941932255734603263170) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (164 - x)) = _
  rw [show 165 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_165 :
    recurrence4B2A4.coeff 165 =
      (((544569581616506495806860385506355723589624158967926164684532164 * 10 ^ 70 +
        7494175810508101038193025624827644021991480364169069912722821043129057) * 10 ^ 70 +
        1701954441430940408184361232501299858017669114459498327533161658694647) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (165 - x)) = _
  rw [show 166 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_166 :
    recurrence4B2A4.coeff 166 =
      -(((603192071379230993010384192626139100196711244756550060904845507 * 10 ^ 70 +
        4729488247368702670277814228261186525247741077667842192804115420847360) * 10 ^ 70 +
        0313316887038195008297674386168652903468481691412702555145510392149588) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (166 - x)) = _
  rw [show 167 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_167 :
    recurrence4B2A4.coeff 167 =
      (((653172553348387704733190475475227725841977255102329798743244907 * 10 ^ 70 +
        0028085554691898025408798434136251432826384205803208604297616246259043) * 10 ^ 70 +
        9019443595383706768284267621842933157791543132855071520999213536657742) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (167 - x)) = _
  rw [show 168 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B2A4_coeff_168 :
    recurrence4B2A4.coeff 168 =
      -(((691135724178506330741877323901965094072848857728052015930773882 * 10 ^ 70 +
        6809120931601924761243616134638482248926314192397254565637658203093493) * 10 ^ 70 +
        1155378644116172189162987606347259351292013101059970350492284166883168) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (168 - x)) = _
  rw [show 169 = 0 +
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (169 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_169 :
    recurrence4B2A4.coeff 169 =
      (((714185485428596330579561350144391694183892163730427850106895594 * 10 ^ 70 +
        8157009256219184576750504613101017683018271209543698568074147724051995) * 10 ^ 70 +
        9767897311788683762875279462137837699362923646399446686355373541476937) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (169 - x)) = _
  rw [show 170 = 0 +
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
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (170 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_170 :
    recurrence4B2A4.coeff 170 =
      -(((720216779307142453974013667871319435420786027098446765039556533 * 10 ^ 70 +
        4124108011370380475916993492504852796999846071452817423499180927884351) * 10 ^ 70 +
        8586818148965289106453879539832983338533547352531291960618166372416121) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (170 - x)) = _
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
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
    rw [show 11 = 9 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (171 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_171 :
    recurrence4B2A4.coeff 171 =
      (((708169323490569380092471736143799798408935569628802785410512049 * 10 ^ 70 +
        6222817138888740054994624837539572511718379842171093823515788181913499) * 10 ^ 70 +
        1641909499110729393065402260584379844529228733475229471102539615994580) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (171 - x)) = _
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
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
    rw [show 12 = 9 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (172 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_172 :
    recurrence4B2A4.coeff 172 =
      -(((678185031195948862328508142565550454081497170480401730773673643 * 10 ^ 70 +
        3095139892440717601483719676714005233005994837834578178611698931630565) * 10 ^ 70 +
        4503173021371764149330693184335863697218784613669505122432512939326698) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (172 - x)) = _
  rw [show 173 = 0 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
    rw [show 13 = 9 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (173 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_173 :
    recurrence4B2A4.coeff 173 =
      (((631642238076300589384230356095553487932896271591922538891116881 * 10 ^ 70 +
        8431757013975045751911971424905040828075315755330615311682395594289137) * 10 ^ 70 +
        0347379705309033390325686812770830829878228017671163027379809419963511) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (173 - x)) = _
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
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
    rw [show 14 = 9 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (174 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_174 :
    recurrence4B2A4.coeff 174 =
      -(((571056530742305150495611114774837472678218370467861636235997267 * 10 ^ 70 +
        6972249276436443028509162999993536718848110411775644287377404348958277) * 10 ^ 70 +
        2287317844374041514334766510856465843873961328129140664571833644286249) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (174 - x)) = _
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
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
    rw [show 15 = 9 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (175 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_175 :
    recurrence4B2A4.coeff 175 =
      (((499857219283767942381786187008882116693841876493668371914245942 * 10 ^ 70 +
        1108784267385709580039135163073171375512507515992849458314724657794459) * 10 ^ 70 +
        7964256814988050242987086263301067769635357539487569153663810559726789) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (175 - x)) = _
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
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
    rw [show 16 = 9 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (176 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_176 :
    recurrence4B2A4.coeff 176 =
      -(((422066874387980961932284356684014569125399358640555090883263904 * 10 ^ 70 +
        2931789418530576405176010079255669699616469284301664919969934533045227) * 10 ^ 70 +
        5420236794323529275528902989218679105651098302006161852957142960997017) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (176 - x)) = _
  rw [show 177 = 0 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
    rw [show 17 = 9 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (177 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_177 :
    recurrence4B2A4.coeff 177 =
      (((341925465212552607628249689881935350831059051589594714514141184 * 10 ^ 70 +
        8483328045124382731863230571993046119455741466923419101932891215146303) * 10 ^ 70 +
        4775811008361785483000961142668924537782472609883546978040957976632010) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (177 - x)) = _
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
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
    rw [show 18 = 9 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (178 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_178 :
    recurrence4B2A4.coeff 178 =
      -(((263507891459384560505336643494481597275850179095785993057898373 * 10 ^ 70 +
        3518210275114658104820440343103546210918078313656466195860166251720914) * 10 ^ 70 +
        1359594484811354258077570923991890066947002911991461082121307754728139) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (178 - x)) = _
  rw [show 179 = 0 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (179 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_179 :
    recurrence4B2A4.coeff 179 =
      (((190382877962047630219587560755610674696847478849103471985389916 * 10 ^ 70 +
        0298649322331734620269704155733266924680249637550573201466100400162244) * 10 ^ 70 +
        9075268528570396587979561554199605598869857759699024333809052540900867) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (179 - x)) = _
  rw [show 180 = 1 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 8 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (180 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (180 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_180 :
    recurrence4B2A4.coeff 180 =
      -(((125352692406901912519467893030347059233224460205533125268119891 * 10 ^ 70 +
        9439833033117540684555264873879726809511130817531201517365887315685404) * 10 ^ 70 +
        7584140674884761855456981334484897368811370977225296755333081492175629) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (180 - x)) = _
  rw [show 181 = 2 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 7 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (181 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (181 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_181 :
    recurrence4B2A4.coeff 181 =
      (((70298850249939519894158561569510983215621688946073547362296485 * 10 ^ 70 +
        8726298463758404092055246882175184899900168763347189970437466684559837) * 10 ^ 70 +
        5146611720249541805917279562332194362841172063396792530443902009208439) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (181 - x)) = _
  rw [show 182 = 3 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 6 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (182 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (182 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_182 :
    recurrence4B2A4.coeff 182 =
      -(((26141801770431118103373782779271511448877150390996266013949300 * 10 ^ 70 +
        9022713230472973344572029923244723782414788899609724479058292299370243) * 10 ^ 70 +
        5380916250235910898263292032977962819568355233870355634780385852081420) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (182 - x)) = _
  rw [show 183 = 4 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (183 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_183 :
    recurrence4B2A4.coeff 183 =
      -(((7094187814103072961371433473982792608714439058687004175341214 * 10 ^ 70 +
        4860849103275702396280328370712098787016045785784679035345542589584939) * 10 ^ 70 +
        5367650380130815208961473111489764320712691105670030322282149497055329) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (183 - x)) = _
  rw [show 184 = 5 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (184 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_184 :
    recurrence4B2A4.coeff 184 =
      (((30133265558152961431373882846928946854677460012370314215660228 * 10 ^ 70 +
        9440056312031720713963442653721646454372652607665480727882397687289381) * 10 ^ 70 +
        4001663038327011752664754390609513090999664021251629654376721141131804) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (184 - x)) = _
  rw [show 185 = 6 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (185 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_185 :
    recurrence4B2A4.coeff 185 =
      -(((44247912640213762662832731349748545675839100640123288076571499 * 10 ^ 70 +
        5552058834473936468442016339953407135345260242980576027571564029356045) * 10 ^ 70 +
        4228570261313693251417813288368424841282388895772592271290668254721674) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (185 - x)) = _
  rw [show 186 = 7 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (186 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_186 :
    recurrence4B2A4.coeff 186 =
      (((51039492011837523225763920884061806890843394154463902503156364 * 10 ^ 70 +
        2874309748139645201331327307600064608713865780998056662856594624260561) * 10 ^ 70 +
        5367836118007721834196278605729604310705328790534954071520716989853015) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (186 - x)) = _
  rw [show 187 = 8 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (187 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_187 :
    recurrence4B2A4.coeff 187 =
      -(((52229254588023775380952823407197853510891057029461733172208613 * 10 ^ 70 +
        4392002813887210094780630075075706428833850926828315564192000337015218) * 10 ^ 70 +
        4364928946412645461535592115968722092376888587675342886398963715189998) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (187 - x)) = _
  rw [show 188 = 9 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4B2A4_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (188 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_188 :
    recurrence4B2A4.coeff 188 =
      (((49482535166656662181985493790283769578529581477539947488704309 * 10 ^ 70 +
        7454355911943167766266491877532920876556111988442881547191539053751165) * 10 ^ 70 +
        4082839578547991830889990287836003837871686698160650480674607649792121) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (188 - x)) = _
  rw [show 189 = 10 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (189 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_189 :
    recurrence4B2A4.coeff 189 =
      -(((44279697623295983143442203366998175240058096500636140253430227 * 10 ^ 70 +
        4889656809440252959274109176327112223845548377009554302665639017231000) * 10 ^ 70 +
        4076372501070927908277187876495301280334071857144117933609382359863985) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (189 - x)) = _
  rw [show 190 = 11 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (190 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_190 :
    recurrence4B2A4.coeff 190 =
      (((37838097148541595954384460852302644758131680493789380842211616 * 10 ^ 70 +
        1387578599796180278939417271455166308027270564704805233433972791458598) * 10 ^ 70 +
        7737110549373412125907720253179295359185626933732663879187914758905121) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (190 - x)) = _
  rw [show 191 = 12 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (191 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_191 :
    recurrence4B2A4.coeff 191 =
      -(((31081489342007601300207378625049300637639037698487437339584405 * 10 ^ 70 +
        8335431495171187180169517164510975397920278898831478875195290324721911) * 10 ^ 70 +
        9723728696255969449707020988190005599506967000164077351630165806066582) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (191 - x)) = _
  rw [show 192 = 13 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (192 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_192 :
    recurrence4B2A4.coeff 192 =
      (((24647896136064416033392903639478364114171325225126563444037519 * 10 ^ 70 +
        7409429670119107601177547716775705943897654947807184113878278546019044) * 10 ^ 70 +
        7204358033747075687480890418209433045078401995115928247137118867635841) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (192 - x)) = _
  rw [show 193 = 14 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (193 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_193 :
    recurrence4B2A4.coeff 193 =
      -(((18924237988843966971234575671583979488245526142142049653054269 * 10 ^ 70 +
        6052119351209351579789855801104928297718250822881947474535757779939143) * 10 ^ 70 +
        7969016972902244765009009573365029426959271801871540851993184255924696) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (193 - x)) = _
  rw [show 194 = 15 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (194 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_194 :
    recurrence4B2A4.coeff 194 =
      (((14095798094713771294407681160663223678425258510743215910638846 * 10 ^ 70 +
        5914144929105335121659453240005210527329796621014386050619666300643324) * 10 ^ 70 +
        7786468723233298982889597671288715497782004281298848211626178326848394) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (194 - x)) = _
  rw [show 195 = 16 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (195 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_195 :
    recurrence4B2A4.coeff 195 =
      -(((10200165288699838741606185638750641257955246216113122357036098 * 10 ^ 70 +
        1106857221601315415974368791797608396415389428127280912698384146841127) * 10 ^ 70 +
        4848568517190593543335448468157941680352628642227683509739850448015029) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (195 - x)) = _
  rw [show 196 = 17 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (196 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_196 :
    recurrence4B2A4.coeff 196 =
      (((7177927092645861755694275241542382551969843330799977564740427 * 10 ^ 70 +
        5144048130320431563133563319080102126169701318794273903218842172994793) * 10 ^ 70 +
        8864185691831212650445557734922936503821643235412279461464741645466807) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (196 - x)) = _
  rw [show 197 = 18 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (197 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_197 :
    recurrence4B2A4.coeff 197 =
      -(((4915315490660395643080805411187436613326709931276797742787367 * 10 ^ 70 +
        4686576909425455322840689309437565754994415977516418666062658387449458) * 10 ^ 70 +
        6573040781874567566868564585358313799269487991693129325718637472763199) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (197 - x)) = _
  rw [show 198 = 19 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (198 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_198 :
    recurrence4B2A4.coeff 198 =
      (((3276679373167342738210241113666875064810112737587359533585081 * 10 ^ 70 +
        4924580478496447698410713394459690943517892663815963129596301947806725) * 10 ^ 70 +
        8224988131183916565261783452154331087834925073160442834192509884989754) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (198 - x)) = _
  rw [show 199 = 20 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (199 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_199 :
    recurrence4B2A4.coeff 199 =
      -(((2126728799267364192580746398098023381000101898621280477000638 * 10 ^ 70 +
        0756792150102203739780480305437146818239911216845553659535994709547351) * 10 ^ 70 +
        1373184177084807359498157894756701771296281092084682832178410138682323) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (199 - x)) = _
  rw [show 200 = 21 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (200 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_200 :
    recurrence4B2A4.coeff 200 =
      (((1343844124510073055770292166612846166790465565290624128762530 * 10 ^ 70 +
        2865003504104487182093611871053632750978099937328315920521475514460955) * 10 ^ 70 +
        3996068370713597403658525183078642777322909488855514604983203845465832) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (200 - x)) = _
  rw [show 201 = 22 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (201 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_201 :
    recurrence4B2A4.coeff 201 =
      -(((826411824046306573220893432529425553111881162912555646350300 * 10 ^ 70 +
        6142460338988360358361849770028548218162552171787487542820738525826051) * 10 ^ 70 +
        7377640570600162003575413859621260951234517084075223274741183889160532) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (201 - x)) = _
  rw [show 202 = 23 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (202 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_202 :
    recurrence4B2A4.coeff 202 =
      (((494283475397210825357194122676733699282081488315550705600047 * 10 ^ 70 +
        5628986875814623507161979775295691910228556610704063189600429464242996) * 10 ^ 70 +
        8711959561967899470671662883614689683855300529738045214330793567893577) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (202 - x)) = _
  rw [show 203 = 24 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (203 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_203 :
    recurrence4B2A4.coeff 203 =
      -(((287237281960925168379380213442858490946834492295733258856204 * 10 ^ 70 +
        1281560217966890452682346090659210964676433515853798870321962493999695) * 10 ^ 70 +
        3663979522230024910064529385595303658875133001841255913800125059163043) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (203 - x)) = _
  rw [show 204 = 25 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (204 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_204 :
    recurrence4B2A4.coeff 204 =
      (((161924965360436954142256714765718969447421484276982521780630 * 10 ^ 70 +
        8307453513939647264497677598225366501630452525785691725407480531908079) * 10 ^ 70 +
        7304255480408438333370674601712966956604957793807858869593396988703396) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (204 - x)) = _
  rw [show 205 = 26 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (205 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_205 :
    recurrence4B2A4.coeff 205 =
      -(((88345247746627597550604985344229211587646576050543379061465 * 10 ^ 70 +
        0944729125827129943774563885004592807609828585014111264007909475195661) * 10 ^ 70 +
        4380627398817974913596803716639839868461824827457812963906169186012431) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (205 - x)) = _
  rw [show 206 = 27 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (206 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_206 :
    recurrence4B2A4.coeff 206 =
      (((46485636310668830006429303369874310411641654697878462109127 * 10 ^ 70 +
        1262445158527248787775901852292045644323490736510901663732688919542511) * 10 ^ 70 +
        6984887759693393857103230967839103468823412817979163116633731799526823) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (206 - x)) = _
  rw [show 207 = 28 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 13 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (207 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_207 :
    recurrence4B2A4.coeff 207 =
      -(((23460299549333503256379512142750205521307873183588639682927 * 10 ^ 70 +
        1989739327165493213633937841340692203172436914931018546620378979017693) * 10 ^ 70 +
        5898437506375488826717419135645429661321874791300320408966943603545980) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (207 - x)) = _
  rw [show 208 = 29 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (208 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_208 :
    recurrence4B2A4.coeff 208 =
      (((11253912919950975392239360968550853457350781441142823489905 * 10 ^ 70 +
        9218626635194476002644715758076946912622299498141411902055923144548711) * 10 ^ 70 +
        1925205011129021083596875952458058069975333500813799716445660386671141) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (208 - x)) = _
  rw [show 209 = 30 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (209 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_209 :
    recurrence4B2A4.coeff 209 =
      -(((5049296226867692087088437926477874115744443456974590995466 * 10 ^ 70 +
        1031093544237341692139019312447598776842133313984846697036554665876380) * 10 ^ 70 +
        3918112193644306548157905704722230527377965756552291577573137257113888) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (209 - x)) = _
  rw [show 210 = 31 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 10 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (210 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_210 :
    recurrence4B2A4.coeff 210 =
      (((2050720590460253431541816781088164222708141287455789075717 * 10 ^ 70 +
        1214140503131395761900243211187186968396101279071477504800080155429137) * 10 ^ 70 +
        0323357318198974958327023646188083755998077946610748171417050387371455) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (210 - x)) = _
  rw [show 211 = 32 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (211 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_211 :
    recurrence4B2A4.coeff 211 =
      -(((693488211905971793172973404724479669441857142585624137527 * 10 ^ 70 +
        6924281582313877147847291112097342240374493056603736454772128187494408) * 10 ^ 70 +
        9979865382563708561578515170279029491382807866465704646623336357083642) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (211 - x)) = _
  rw [show 212 = 33 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 8 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (212 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_212 :
    recurrence4B2A4.coeff 212 =
      (((135237975448393384089732807673070931796155070897373482995 * 10 ^ 70 +
        2771121015267995201731479816152941181727687175157838833515381220057913) * 10 ^ 70 +
        3831374681214947810475547108862180699116294798463370040901755860732301) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (212 - x)) = _
  rw [show 213 = 34 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (213 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_213 :
    recurrence4B2A4.coeff 213 =
      (((58363059668905961195141815345410933520774792965796737690 * 10 ^ 70 +
        0319221287156673241900268112076183765494747342983056384099121483832055) * 10 ^ 70 +
        1087064414410350376081276182893033723387073296503845873970104579059426) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (213 - x)) = _
  rw [show 214 = 35 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (214 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_214 :
    recurrence4B2A4.coeff 214 =
      -(((100230966719520844956904052787434043681570274472320763171 * 10 ^ 70 +
        4567705575063618631546313997376905138232537005036940419591735473655649) * 10 ^ 70 +
        3799409708092660139034168495977529646964237252803012098315747002550510) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (214 - x)) = _
  rw [show 215 = 36 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (215 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_215 :
    recurrence4B2A4.coeff 215 =
      (((88302140807613370598344718788905848964774491282685754875 * 10 ^ 70 +
        3836386264840991010756339412243384317862846557908216667494517650531304) * 10 ^ 70 +
        9284624594515893853865154185886294325368310489170903168841103870941525) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (215 - x)) = _
  rw [show 216 = 37 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
