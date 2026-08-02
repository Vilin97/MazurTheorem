/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A4Square coefficient convolution

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

theorem recurrence4A4Square_coeff_0 :
    recurrence4A4Square.coeff 0 =
      (148021789696 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_1 :
    recurrence4A4Square.coeff 1 =
      (-427842316979968 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_2 :
    recurrence4A4Square.coeff 2 =
      (-353249410707235440 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_3 :
    recurrence4A4Square.coeff 3 =
      (1717494371245297057808 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_4 :
    recurrence4A4Square.coeff 4 =
      (-465779060122729549493484 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_5 :
    recurrence4A4Square.coeff 5 =
      (-1560002716544997716614732768 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_6 :
    recurrence4A4Square.coeff 6 =
      (1242487726523214483709488418128 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_7 :
    recurrence4A4Square.coeff 7 =
      (-245545287342814637297941293063716 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_8 :
    recurrence4A4Square.coeff 8 =
      (-25033201182462074600222702570656635 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_9 :
    recurrence4A4Square.coeff 9 =
      (9875920664515501296764794605564444276 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_10 :
    recurrence4A4Square.coeff 10 =
      (1138854270323942327991259036836003404790 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_11 :
    recurrence4A4Square.coeff 11 =
      (-863335021728656556914413624207044082999714 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_12 :
    recurrence4A4Square.coeff 12 =
      (244887380994046862782991058113134748681098341 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_13 :
    recurrence4A4Square.coeff 13 =
      (-56131203277605832225004761397076172069752040616 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_14 :
    recurrence4A4Square.coeff 14 =
      (10199383750323007119229822233373139521144275025377 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_15 :
    recurrence4A4Square.coeff 15 =
      (-1493854885895251672689070305521876408946782439072336 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_16 :
    recurrence4A4Square.coeff 16 =
      (235209385074561622161184413127582273796747881946364034 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_17 :
    recurrence4A4Square.coeff 17 =
      (-59227865196703722859695512602528279601299001257326887312 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_18 :
    recurrence4A4Square.coeff 18 =
      (18933797018402706125356206926955818920370344009859550870075 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_19 :
    recurrence4A4Square.coeff 19 =
      (-5551668634933289647327646217118214927980128300983897577418350 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_20 :
    recurrence4A4Square.coeff 20 =
      (1392609293560938537857287271891678525528422403968573418287992164 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_21 :
    recurrence4A4Square.coeff 21 =
      (-301638371394444593681176886553808242419191059534352301611500363648 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_22 :
    recurrence4A4Square.coeff 22 =
      (57382130648246866423856034797781051913838093079916165684127820533189 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_23 :
    recurrence4A4Square.coeff 23 =
      (-9713982829728277004411482616930182093497888081399146977061925841588034 : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_24 :
    recurrence4A4Square.coeff 24 =
      ((147 * 10 ^ 70 +
        7017000926830094692229373155863887566820430088532905173988562594999912) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_25 :
    recurrence4A4Square.coeff 25 =
      -((20309 * 10 ^ 70 +
        7849183642375218788034362208002162491602850001694756625906705506434512) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_26 :
    recurrence4A4Square.coeff 26 =
      ((2539088 * 10 ^ 70 +
        9009997303745238112724744858113596553829144982383195424053784060107489) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_27 :
    recurrence4A4Square.coeff 27 =
      -((289886787 * 10 ^ 70 +
        0602300892307490562533511076040499452691536153497868992963703015372382) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_28 :
    recurrence4A4Square.coeff 28 =
      ((30340296299 * 10 ^ 70 +
        4882729650832885454318576382522755121504573411809160189324127898062454) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_29 :
    recurrence4A4Square.coeff 29 =
      -((2920965414513 * 10 ^ 70 +
        8410934306655376159706497270634007568374222643820503127110839018674444) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_30 :
    recurrence4A4Square.coeff 30 =
      ((259464097037638 * 10 ^ 70 +
        4487772532528686041354574186957395327153248693310629773846771920989422) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_31 :
    recurrence4A4Square.coeff 31 =
      -((21324759644101472 * 10 ^ 70 +
        8677778227570543161056149267121702578574968321968230955346716508986348) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_32 :
    recurrence4A4Square.coeff 32 =
      ((1625777228509233192 * 10 ^ 70 +
        6038549779397216238995111369557329488093692056900051697177340171286884) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (32 - x)) = _
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

theorem recurrence4A4Square_coeff_33 :
    recurrence4A4Square.coeff 33 =
      -((115249412387239811156 * 10 ^ 70 +
        9037210462540109531265675683582498209457475573126305758442885079106356) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (33 - x)) = _
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

theorem recurrence4A4Square_coeff_34 :
    recurrence4A4Square.coeff 34 =
      ((7613353584507259401596 * 10 ^ 70 +
        0815720072740956389793506350801768981721039042535617640806868594592354) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (34 - x)) = _
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

theorem recurrence4A4Square_coeff_35 :
    recurrence4A4Square.coeff 35 =
      -((469643906547481079272137 * 10 ^ 70 +
        9418757231359737992635439107297405676116618199689502291051562830989778) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (35 - x)) = _
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

theorem recurrence4A4Square_coeff_36 :
    recurrence4A4Square.coeff 36 =
      ((27105469302631421718053607 * 10 ^ 70 +
        7162928852849461948666327618660079404111785567159711227213102542483661) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (36 - x)) = _
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

theorem recurrence4A4Square_coeff_37 :
    recurrence4A4Square.coeff 37 =
      -((1466328321360141764395649601 * 10 ^ 70 +
        4459370821130360792026505169127695117925665445574561618580703058666954) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (37 - x)) = _
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

theorem recurrence4A4Square_coeff_38 :
    recurrence4A4Square.coeff 38 =
      ((74479630122057456978616370466 * 10 ^ 70 +
        3846858126340372002442941338620944194145195258521545102793006461111323) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (38 - x)) = _
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

theorem recurrence4A4Square_coeff_39 :
    recurrence4A4Square.coeff 39 =
      -((3557799527185097731456903473552 * 10 ^ 70 +
        3611844819964928888993134613613994070661053461299874234945394175469444) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (39 - x)) = _
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

theorem recurrence4A4Square_coeff_40 :
    recurrence4A4Square.coeff 40 =
      ((160078199682722428824306228042319 * 10 ^ 70 +
        7737756941569643900751472203794618741519819836873930463413612070523774) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (40 - x)) = _
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

theorem recurrence4A4Square_coeff_41 :
    recurrence4A4Square.coeff 41 =
      -((6793996579071508496319421801096998 * 10 ^ 70 +
        1551545952674333786083661803128278825848799350026617317535832668712984) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (41 - x)) = _
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

theorem recurrence4A4Square_coeff_42 :
    recurrence4A4Square.coeff 42 =
      ((272374131273721250962843206531366645 * 10 ^ 70 +
        3181329799922082674382183641837120241722781022586140702245882736859168) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (42 - x)) = _
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

theorem recurrence4A4Square_coeff_43 :
    recurrence4A4Square.coeff 43 =
      -((10328339949399742381899780985751487069 * 10 ^ 70 +
        6552187892705033642499997641615064384879215729782279986650652461107894) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (43 - x)) = _
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

theorem recurrence4A4Square_coeff_44 :
    recurrence4A4Square.coeff 44 =
      ((370911176667840646023232464891821982419 * 10 ^ 70 +
        6002071065371414596091819190451196174561435932041597793921081493911447) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (44 - x)) = _
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

theorem recurrence4A4Square_coeff_45 :
    recurrence4A4Square.coeff 45 =
      -((12630204996011675801023260050384737844591 * 10 ^ 70 +
        4846981639645300106124522716314981844015207227574541480016320020451430) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (45 - x)) = _
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

theorem recurrence4A4Square_coeff_46 :
    recurrence4A4Square.coeff 46 =
      ((408277785254794470004959699552044491715921 * 10 ^ 70 +
        1232069212363050207559963206747288316285436368959381069112578457425972) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (46 - x)) = _
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

theorem recurrence4A4Square_coeff_47 :
    recurrence4A4Square.coeff 47 =
      -((12542632629347184338850945998043163122049698 * 10 ^ 70 +
        6825895969008644618165647691349337050635294754247911817819246678359978) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (47 - x)) = _
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

theorem recurrence4A4Square_coeff_48 :
    recurrence4A4Square.coeff 48 =
      ((366582967070363032684901213150133775225179737 * 10 ^ 70 +
        1384082717788593379289789561489459130613080131668606169020528983399561) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (48 - x)) = _
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

theorem recurrence4A4Square_coeff_49 :
    recurrence4A4Square.coeff 49 =
      -((10203543958520269722840532366009829883595844611 * 10 ^ 70 +
        3949627617522550524434051446533800159798947493673815985304269343510560) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (49 - x)) = _
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

theorem recurrence4A4Square_coeff_50 :
    recurrence4A4Square.coeff 50 =
      ((270739835162477625835079457627396391622318530169 * 10 ^ 70 +
        7447679192116595282060049221565039873119732956427584082248665039660634) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (50 - x)) = _
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

theorem recurrence4A4Square_coeff_51 :
    recurrence4A4Square.coeff 51 =
      -((6854668792789353363395305116685895312322153449916 * 10 ^ 70 +
        1213910996263740111291752677441133269267423313349793589848235978169440) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (51 - x)) = _
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

theorem recurrence4A4Square_coeff_52 :
    recurrence4A4Square.coeff 52 =
      ((165748417232311440666361105755242829044255099679294 * 10 ^ 70 +
        0387959936514862049974045308037242155398536885812478431756447915089235) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (52 - x)) = _
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

theorem recurrence4A4Square_coeff_53 :
    recurrence4A4Square.coeff 53 =
      -((3831084493525834812356134488719970922878491271205216 * 10 ^ 70 +
        7584656381691800048802569887671756512448518571769384189064647212682742) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (53 - x)) = _
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

theorem recurrence4A4Square_coeff_54 :
    recurrence4A4Square.coeff 54 =
      ((84716991153909739769616233711226865709116498715325313 * 10 ^ 70 +
        1023065714074220345718803240864515291977267267147575582734017519561683) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (54 - x)) = _
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

theorem recurrence4A4Square_coeff_55 :
    recurrence4A4Square.coeff 55 =
      -((1793699604822201842055250885099432653994234740726682017 * 10 ^ 70 +
        5139460181796902905654617563994911282020923019490502544614254200666768) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (55 - x)) = _
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

theorem recurrence4A4Square_coeff_56 :
    recurrence4A4Square.coeff 56 =
      ((36391572929052260425590291732395312128123606997799557035 * 10 ^ 70 +
        3700408283222129665778396327040316532996273115174179895900589717055890) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (56 - x)) = _
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

theorem recurrence4A4Square_coeff_57 :
    recurrence4A4Square.coeff 57 =
      -((708033150896997253111034356288370945466612875849831324414 * 10 ^ 70 +
        6800715305862908962304867287794536760547562253095607205397649696701974) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (57 - x)) = _
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

theorem recurrence4A4Square_coeff_58 :
    recurrence4A4Square.coeff 58 =
      ((13219849198314152028171966646026919303420467811657699754834 * 10 ^ 70 +
        7789949738338298857152030054816522542960326565012600105498627749162488) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (58 - x)) = _
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

theorem recurrence4A4Square_coeff_59 :
    recurrence4A4Square.coeff 59 =
      -((237043115080937333902329900530653874348089649965888194334927 * 10 ^ 70 +
        7724800731831219392536295393746696227895044596667582158260778881375324) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (59 - x)) = _
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

theorem recurrence4A4Square_coeff_60 :
    recurrence4A4Square.coeff 60 =
      ((4084639305529518431310446317258505967130873012223247152549601 * 10 ^ 70 +
        2247184839184923819887123294754979329289858658782664139827026371656984) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (60 - x)) = _
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

theorem recurrence4A4Square_coeff_61 :
    recurrence4A4Square.coeff 61 =
      -((67685157165518814365387468355101383529038602436771377007415138 * 10 ^ 70 +
        4306664081582345004633150374781230344720785652149427047963825335647138) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (61 - x)) = _
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

theorem recurrence4A4Square_coeff_62 :
    recurrence4A4Square.coeff 62 =
      ((1079257470601903701166049031511599603767791742023164010946516745 * 10 ^ 70 +
        1831309709753616778367182456537881709054680558039619373262179437096462) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (62 - x)) = _
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

theorem recurrence4A4Square_coeff_63 :
    recurrence4A4Square.coeff 63 =
      -((16569835596491028330801188210732357536976914292817159357955116623 * 10 ^ 70 +
        1997688710234508517243725268071750761661735042091370942144487071571326) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (63 - x)) = _
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

theorem recurrence4A4Square_coeff_64 :
    recurrence4A4Square.coeff 64 =
      ((245094713463240100157587165525978555659034467846150956310784611052 * 10 ^ 70 +
        2565916812960176191817897787050932763055071809365892606475415848705663) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (64 - x)) = _
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

theorem recurrence4A4Square_coeff_65 :
    recurrence4A4Square.coeff 65 =
      -((3494823289923488114607545549469021063172124353023269416553158598233 * 10 ^ 70 +
        3988009861982323367156686066610954407646959749909971273539936526557676) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (65 - x)) = _
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

theorem recurrence4A4Square_coeff_66 :
    recurrence4A4Square.coeff 66 =
      ((48065904791604830108226159563794406806421576834032565584998256551283 * 10 ^ 70 +
        5347218432521577878716214059762603131477626149990304798412105564518288) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (66 - x)) = _
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

theorem recurrence4A4Square_coeff_67 :
    recurrence4A4Square.coeff 67 =
      -((637980227623373249007430717357007768914547219291287917986037926550053 * 10 ^ 70 +
        1961889156427101711829020557460243918240765147547597765941134570762534) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (67 - x)) = _
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

theorem recurrence4A4Square_coeff_68 :
    recurrence4A4Square.coeff 68 =
      ((8176470397405672397196695480831887877738050544873382220373544589702747 * 10 ^ 70 +
        8392821774945171780722738098709213982665340903855614248422374885903085) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (68 - x)) = _
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

theorem recurrence4A4Square_coeff_69 :
    recurrence4A4Square.coeff 69 =
      -(((10 * 10 ^ 70 +
        1236352808806093239817300900527607061422973765681655840163764008283830) * 10 ^ 70 +
        5005118230504138906945922463309078182054937958457308248845237612360854) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (69 - x)) = _
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

theorem recurrence4A4Square_coeff_70 :
    recurrence4A4Square.coeff 70 =
      (((121 * 10 ^ 70 +
        1534643685817519413433339731003074014794538053102062300213004932093038) * 10 ^ 70 +
        6227950585070902001303901505155087438073789219707008036104929522782558) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (70 - x)) = _
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

theorem recurrence4A4Square_coeff_71 :
    recurrence4A4Square.coeff 71 =
      -(((1402 * 10 ^ 70 +
        0846868475353084867545266195341901481367287691888685888565353370142222) * 10 ^ 70 +
        6789606501061443759987784874581612625816908688300022652437053010996406) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (71 - x)) = _
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

theorem recurrence4A4Square_coeff_72 :
    recurrence4A4Square.coeff 72 =
      (((15698 * 10 ^ 70 +
        4176882582775400738189851525001734291444210583608805700826298282204633) * 10 ^ 70 +
        9699829461184653157267822790436347629251710004326739701168138824292494) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (72 - x)) = _
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

theorem recurrence4A4Square_coeff_73 :
    recurrence4A4Square.coeff 73 =
      -(((170129 * 10 ^ 70 +
        2375706269731522003957751769832931112240464554743471261178567330394465) * 10 ^ 70 +
        0338236985506304565588556395169799914665534545096927764144324322715528) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (73 - x)) = _
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

theorem recurrence4A4Square_coeff_74 :
    recurrence4A4Square.coeff 74 =
      (((1785401 * 10 ^ 70 +
        7602956900639606485236896879462828107609519892399576604616109022252701) * 10 ^ 70 +
        3236785470417773427356119689266842492808924066032586329663729633943767) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (74 - x)) = _
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

theorem recurrence4A4Square_coeff_75 :
    recurrence4A4Square.coeff 75 =
      -(((18151555 * 10 ^ 70 +
        5976489777653766258799973698277840510537522761421762218903601075861559) * 10 ^ 70 +
        1505539790075715352403573488452531572956725396822757406927280271414730) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (75 - x)) = _
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

theorem recurrence4A4Square_coeff_76 :
    recurrence4A4Square.coeff 76 =
      (((178852190 * 10 ^ 70 +
        3486976349903797013658556562002695074193471850961370272390381676579361) * 10 ^ 70 +
        4063518924553775367789715744443862950018039914879529144765060157770245) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (76 - x)) = _
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

theorem recurrence4A4Square_coeff_77 :
    recurrence4A4Square.coeff 77 =
      -(((1708652270 * 10 ^ 70 +
        3040379915703962603633780378201400038377969106502087706718510611287126) * 10 ^ 70 +
        5174726702376328215921389764604103857056693787437073366803237205513856) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (77 - x)) = _
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

theorem recurrence4A4Square_coeff_78 :
    recurrence4A4Square.coeff 78 =
      (((15833015997 * 10 ^ 70 +
        2208771919317759951038335429454001582267343039087090668264606733743423) * 10 ^ 70 +
        9686171222479112293778196078787243458894387701901529842879324514910743) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (78 - x)) = _
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

theorem recurrence4A4Square_coeff_79 :
    recurrence4A4Square.coeff 79 =
      -(((142360951520 * 10 ^ 70 +
        1037682921942781565147161531759412947747837096873916852161600032586555) * 10 ^ 70 +
        4326926795962454191102499988762759618827734403993814493576077975132042) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (79 - x)) = _
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

theorem recurrence4A4Square_coeff_80 :
    recurrence4A4Square.coeff 80 =
      (((1242503099071 * 10 ^ 70 +
        5919445767979660390912932799987673880692940117636878157401503929839940) * 10 ^ 70 +
        6031143769036556598362498931326336109656133793323967099031654145413100) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (80 - x)) = _
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

theorem recurrence4A4Square_coeff_81 :
    recurrence4A4Square.coeff 81 =
      -(((10530307798575 * 10 ^ 70 +
        0118293315350349261390068848860762242410939504442699563511340491671326) * 10 ^ 70 +
        2089313794708357924325934723479250980326827949839142571924539933173392) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (81 - x)) = _
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

theorem recurrence4A4Square_coeff_82 :
    recurrence4A4Square.coeff 82 =
      (((86691182332666 * 10 ^ 70 +
        8753058026025789890046191382373497766884754487679408250172486073983574) * 10 ^ 70 +
        9830387345781753270134298270525753248786986646429515306959869360882927) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (82 - x)) = _
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

theorem recurrence4A4Square_coeff_83 :
    recurrence4A4Square.coeff 83 =
      -(((693502707678186 * 10 ^ 70 +
        6280279621774109213121882412847176459488294522813557480167015671421725) * 10 ^ 70 +
        0006863285090688084811836651763965032419221219330241006821901421793668) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (83 - x)) = _
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

theorem recurrence4A4Square_coeff_84 :
    recurrence4A4Square.coeff 84 =
      (((5392694469944563 * 10 ^ 70 +
        6635402414393251905250954501389097511454072779175547154611102846489448) * 10 ^ 70 +
        3413339129855917221698125154564156746946015891364299357149512776040430) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (84 - x)) = _
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

theorem recurrence4A4Square_coeff_85 :
    recurrence4A4Square.coeff 85 =
      -(((40774534277927273 * 10 ^ 70 +
        0159485322033389681505779490973678323563860996870371613435433102379243) * 10 ^ 70 +
        7012153169925902343808545227834669838800653788821559050009488679911012) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (85 - x)) = _
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

theorem recurrence4A4Square_coeff_86 :
    recurrence4A4Square.coeff 86 =
      (((299871409754196118 * 10 ^ 70 +
        6693878651380710768307825709750314501715688895246687426180819473013644) * 10 ^ 70 +
        3134060390140302952040838947050437191914906571167671777526163433890548) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (86 - x)) = _
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

theorem recurrence4A4Square_coeff_87 :
    recurrence4A4Square.coeff 87 =
      -(((2145742525425643424 * 10 ^ 70 +
        9818294316546171879761937625558088101526774947241257208816002587627837) * 10 ^ 70 +
        5684423937733157639096709132654025285183255477525222476988922493035918) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (87 - x)) = _
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

theorem recurrence4A4Square_coeff_88 :
    recurrence4A4Square.coeff 88 =
      (((14943306988411491839 * 10 ^ 70 +
        5065099365752871229127728665694081332705200517212686283410157002276925) * 10 ^ 70 +
        1916622040997604657083859537795700797952493585794931207965902629613688) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (88 - x)) = _
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

theorem recurrence4A4Square_coeff_89 :
    recurrence4A4Square.coeff 89 =
      -(((101313892370570571371 * 10 ^ 70 +
        9406935964649570946702012689236325195845509701788762073305659210766718) * 10 ^ 70 +
        1621569680117544807988028372383328065484794103150717653078820112425802) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (89 - x)) = _
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

theorem recurrence4A4Square_coeff_90 :
    recurrence4A4Square.coeff 90 =
      (((668910032938026433797 * 10 ^ 70 +
        6506335478206286670907190716541127566644965694800418243887912978596440) * 10 ^ 70 +
        9163976103701348193460214225346298091954281400669217311327471989964826) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (90 - x)) = _
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

theorem recurrence4A4Square_coeff_91 :
    recurrence4A4Square.coeff 91 =
      -(((4301925121105871829782 * 10 ^ 70 +
        9399210851313506693258210906957746962772851971164064523342048339479673) * 10 ^ 70 +
        9972846764348826979731535901862643665601865075121653409093271301013748) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (91 - x)) = _
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

theorem recurrence4A4Square_coeff_92 :
    recurrence4A4Square.coeff 92 =
      (((26956981160551674745347 * 10 ^ 70 +
        0466641364111463012284991554334250390955318710489934701553953035886681) * 10 ^ 70 +
        5598574853509032395628159910914853024073583665354110741920399927808224) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (92 - x)) = _
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

theorem recurrence4A4Square_coeff_93 :
    recurrence4A4Square.coeff 93 =
      -(((164629141768510058510261 * 10 ^ 70 +
        4793903945037670582852661840301217533681651175777424269109405145607626) * 10 ^ 70 +
        2325634508809585502421664753932464893521585100140667376309507706285770) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (93 - x)) = _
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

theorem recurrence4A4Square_coeff_94 :
    recurrence4A4Square.coeff 94 =
      (((980121752978857754811432 * 10 ^ 70 +
        3500599300892779756420644949984771474157427387205726046817059417931681) * 10 ^ 70 +
        4211535798270469651148258094887096094641677319649162790442732274206597) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (94 - x)) = _
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

theorem recurrence4A4Square_coeff_95 :
    recurrence4A4Square.coeff 95 =
      -(((5689827652863679885945254 * 10 ^ 70 +
        3167933395146337215288690643335084020196008028200477110216164280514842) * 10 ^ 70 +
        2468078252546915455254442000373881174084190226353814803330565262844976) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (95 - x)) = _
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

theorem recurrence4A4Square_coeff_96 :
    recurrence4A4Square.coeff 96 =
      (((32215811277337237311843844 * 10 ^ 70 +
        4544384870660888052076235498367384871983768264877503365300232343058265) * 10 ^ 70 +
        7289204935790351519480513135884940434183831880685141760326447245730666) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (96 - x)) = _
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

theorem recurrence4A4Square_coeff_97 :
    recurrence4A4Square.coeff 97 =
      -(((177947663756419691664463046 * 10 ^ 70 +
        8200342838805517126415062660011498561825506255885177158164830927403520) * 10 ^ 70 +
        1568951455222745155631880992205612818763320901834422007247843281438292) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (97 - x)) = _
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

theorem recurrence4A4Square_coeff_98 :
    recurrence4A4Square.coeff 98 =
      (((959110166725786317278873333 * 10 ^ 70 +
        6475262766791002041052505020389176244863687645515975433593191239615688) * 10 ^ 70 +
        9382306035359777588131050468504053269079937568191683643040925570407578) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (98 - x)) = _
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

theorem recurrence4A4Square_coeff_99 :
    recurrence4A4Square.coeff 99 =
      -(((5045391080830939695602557225 * 10 ^ 70 +
        4552384734110005118051034703235229462615239749199824638050778682802796) * 10 ^ 70 +
        3947365961209768380924589062827247373535259313939128504373237115566818) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (99 - x)) = _
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

theorem recurrence4A4Square_coeff_100 :
    recurrence4A4Square.coeff 100 =
      (((25909913046638331367009347535 * 10 ^ 70 +
        8704826708530155281229315849278656340676589534757083995206664887898385) * 10 ^ 70 +
        4754524691449511534156014823273491857002417530116762226913215949720750) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (100 - x)) = _
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

theorem recurrence4A4Square_coeff_101 :
    recurrence4A4Square.coeff 101 =
      -(((129919416053747677098383990592 * 10 ^ 70 +
        9404985505294396681169537513457893216556210786061038904389626240858255) * 10 ^ 70 +
        0840263524119473555113549016730842320564480928111737911078152132905848) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (101 - x)) = _
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

theorem recurrence4A4Square_coeff_102 :
    recurrence4A4Square.coeff 102 =
      (((636222433970374568701592777460 * 10 ^ 70 +
        0261187351745507664163221408026247826561237138649286899885697405972758) * 10 ^ 70 +
        9096498070785464870491937717646782206839144847789847772156391826272737) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (102 - x)) = _
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

theorem recurrence4A4Square_coeff_103 :
    recurrence4A4Square.coeff 103 =
      -(((3043394365481115963301083020889 * 10 ^ 70 +
        9334166646844306701140112239431733708694205694346153334184231108501964) * 10 ^ 70 +
        3248520359909938824247406259190784306927046332641611756325713461071822) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (103 - x)) = _
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

theorem recurrence4A4Square_coeff_104 :
    recurrence4A4Square.coeff 104 =
      (((14223520093087037089623099725539 * 10 ^ 70 +
        0454839014346647140185129341550501197741576419837730130918258959246237) * 10 ^ 70 +
        2074244388768023993068130334806321155226394582500140224670216857411420) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (104 - x)) = _
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

theorem recurrence4A4Square_coeff_105 :
    recurrence4A4Square.coeff 105 =
      -(((64958895709119057271518929948668 * 10 ^ 70 +
        8601098700986306196583051670012188450339418107418678844703695556716974) * 10 ^ 70 +
        4885554038231882574589020258885793324422862569161393936510188309985056) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (105 - x)) = _
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

theorem recurrence4A4Square_coeff_106 :
    recurrence4A4Square.coeff 106 =
      (((289957138678144205254735688749791 * 10 ^ 70 +
        3523988757096910484111227632324694562362236220779103149338906933911924) * 10 ^ 70 +
        9568597400461008167390618613336924486206611565989414111020967138363470) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (106 - x)) = _
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

theorem recurrence4A4Square_coeff_107 :
    recurrence4A4Square.coeff 107 =
      -(((1265235800257924475318266790682718 * 10 ^ 70 +
        2497228147639392176600899078776115193506700955270351121935643138212349) * 10 ^ 70 +
        4893129550026176167761077731683804256416842851400721506190387297079630) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (107 - x)) = _
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

theorem recurrence4A4Square_coeff_108 :
    recurrence4A4Square.coeff 108 =
      (((5397945189658800281095996618576143 * 10 ^ 70 +
        9960408922834276068501033573248162738398476462231590948964629423323759) * 10 ^ 70 +
        3695259826430974429620232997475042252126693820020929876839582288085811) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (108 - x)) = _
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

theorem recurrence4A4Square_coeff_109 :
    recurrence4A4Square.coeff 109 =
      -(((22520584706548924053422373420879169 * 10 ^ 70 +
        9260187714136016322457034412908585540592182737598284798006976467284689) * 10 ^ 70 +
        8552318285814049259918660770382029484040541222957567810395619056763656) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (109 - x)) = _
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

theorem recurrence4A4Square_coeff_110 :
    recurrence4A4Square.coeff 110 =
      (((91896290249053689272254020603020709 * 10 ^ 70 +
        7103149783393714523857119901335759844177463418988078081507870652780650) * 10 ^ 70 +
        9546829773304708395033580582233292527143087397853356476171674988515237) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (110 - x)) = _
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

theorem recurrence4A4Square_coeff_111 :
    recurrence4A4Square.coeff 111 =
      -(((366821241372714869281156667301802204 * 10 ^ 70 +
        1675816251720345604092184593339380637619520997940841224732525975250828) * 10 ^ 70 +
        8781013275540193953309086098113935240061036949924420752224222478702072) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (111 - x)) = _
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

theorem recurrence4A4Square_coeff_112 :
    recurrence4A4Square.coeff 112 =
      (((1432578301618874266950209517363219070 * 10 ^ 70 +
        0934795715173208127601434420521799699882224466860641898860959857524409) * 10 ^ 70 +
        2579819086226853713881245524139812808083236650670400658534511452708194) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (112 - x)) = _
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

theorem recurrence4A4Square_coeff_113 :
    recurrence4A4Square.coeff 113 =
      -(((5474659131042137173370436277190642624 * 10 ^ 70 +
        3023591744138561610157666907777316428712173013303524610418146315260378) * 10 ^ 70 +
        2505938429830638909388999185505484976602664670297691306012130937118976) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (113 - x)) = _
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

theorem recurrence4A4Square_coeff_114 :
    recurrence4A4Square.coeff 114 =
      (((20475584050149818403307982618746170510 * 10 ^ 70 +
        3089276401240169793151869811950838808651667539699020804878645639543301) * 10 ^ 70 +
        2665653984143472165002148183438885142330236295853455226174547050410820) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (114 - x)) = _
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

theorem recurrence4A4Square_coeff_115 :
    recurrence4A4Square.coeff 115 =
      -(((74958343802990487650432096140980775471 * 10 ^ 70 +
        5683855481720162239647891561164058876677059741754163275071380957709495) * 10 ^ 70 +
        8614905763424966472315378382953908247107732268479304301081102669496870) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (115 - x)) = _
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

theorem recurrence4A4Square_coeff_116 :
    recurrence4A4Square.coeff 116 =
      (((268639849892015564157038053271085077549 * 10 ^ 70 +
        8644250178332215565483864373169561736660702981104535550660967595408081) * 10 ^ 70 +
        1984978756935689009608854996406666341766853454891657672289582119851134) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (116 - x)) = _
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

theorem recurrence4A4Square_coeff_117 :
    recurrence4A4Square.coeff 117 =
      -(((942645352370670324555443627562534231648 * 10 ^ 70 +
        5332048660289219197585292274211173688555435361260238247838790212178377) * 10 ^ 70 +
        4052791763041922898656711139627103356027414601991521194685072933945380) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (117 - x)) = _
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

theorem recurrence4A4Square_coeff_118 :
    recurrence4A4Square.coeff 118 =
      (((3239013385918346317421066688207094440012 * 10 ^ 70 +
        0440564053213499477324411766416186967504720076953546322214162045564477) * 10 ^ 70 +
        3984219126005772870678449616636262027347162471129347515621656032380149) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (118 - x)) = _
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

theorem recurrence4A4Square_coeff_119 :
    recurrence4A4Square.coeff 119 =
      -(((10899866825679694014300868933026455625886 * 10 ^ 70 +
        8861418549366717702198359648002757103026204829616676177201071494492391) * 10 ^ 70 +
        6532649568166566290749394506731264075042405300052982755872265580967442) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (119 - x)) = _
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

theorem recurrence4A4Square_coeff_120 :
    recurrence4A4Square.coeff 120 =
      (((35927721266290084259409332230566357350755 * 10 ^ 70 +
        3001022890082543232775308918695699050845773105471632363512187901290593) * 10 ^ 70 +
        2845233871085974417870754404917811707317649341182273127264480806277595) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (120 - x)) = _
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

theorem recurrence4A4Square_coeff_121 :
    recurrence4A4Square.coeff 121 =
      -(((116009269042441852720328432731476135236176 * 10 ^ 70 +
        9722719309355879984668302983697821006022387342978247760207247048269878) * 10 ^ 70 +
        7372325851057002018304042295554807247792795672751983555784046136972640) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (121 - x)) = _
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

theorem recurrence4A4Square_coeff_122 :
    recurrence4A4Square.coeff 122 =
      (((366997656242311311811704556721613110340491 * 10 ^ 70 +
        5022573584107096745970358618095891368778573763311789277948064030036889) * 10 ^ 70 +
        6712827239850517648891740575056165015765889040762627528438671609160846) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (122 - x)) = _
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

theorem recurrence4A4Square_coeff_123 :
    recurrence4A4Square.coeff 123 =
      -(((1137609190715598051702148969578334268181821 * 10 ^ 70 +
        3173805012108829450530100543396333649157315403844861909173058133982972) * 10 ^ 70 +
        6558408467297319629647858919278954002126224224556491510208703853337126) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (123 - x)) = _
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

theorem recurrence4A4Square_coeff_124 :
    recurrence4A4Square.coeff 124 =
      (((3455670413405688074530237671156686260051269 * 10 ^ 70 +
        5943309364065925794097253963019569079717264138997275246700898822651108) * 10 ^ 70 +
        2304936569226453739743859041672289823769056688575064890227544715629272) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (124 - x)) = _
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

theorem recurrence4A4Square_coeff_125 :
    recurrence4A4Square.coeff 125 =
      -(((10287972858233739962584954620877398331027236 * 10 ^ 70 +
        4123502461168793824050558328968271156926032624535055333918817651173165) * 10 ^ 70 +
        9468628305170761053883440545702287271611532696767733346114955173131730) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (125 - x)) = _
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

theorem recurrence4A4Square_coeff_126 :
    recurrence4A4Square.coeff 126 =
      (((30021548367210151162878443578298128337615855 * 10 ^ 70 +
        1967483514366229133127123569764929337139834910104436077196153038840917) * 10 ^ 70 +
        3801333566053970953527576527857419251015896123367562523180103613321816) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (126 - x)) = _
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

theorem recurrence4A4Square_coeff_127 :
    recurrence4A4Square.coeff 127 =
      -(((85879269676727458762588286581004881497068832 * 10 ^ 70 +
        6684918244634158534931459260396443783877048297140098010994877945868938) * 10 ^ 70 +
        9039339880816718410428318962428071823156304992628989870109126638183600) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (127 - x)) = _
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

theorem recurrence4A4Square_coeff_128 :
    recurrence4A4Square.coeff 128 =
      (((240846579165004518527851426370427938370466660 * 10 ^ 70 +
        3384477249335635765348939134753525889378235029464635427769602222349101) * 10 ^ 70 +
        4242543411091847857818677283264552372530681081702132632103781408039041) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (128 - x)) = _
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

theorem recurrence4A4Square_coeff_129 :
    recurrence4A4Square.coeff 129 =
      -(((662267052792101979415196405611436414752391792 * 10 ^ 70 +
        0383563217652800314658314328972248342957551442181981841602969319106702) * 10 ^ 70 +
        0869921532979493955825270105209784130222511725672912390993934192978210) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (129 - x)) = _
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

theorem recurrence4A4Square_coeff_130 :
    recurrence4A4Square.coeff 130 =
      (((1785701030151546051933777733904548140764448619 * 10 ^ 70 +
        0407071967863805100674718687397221012006751084692370896613669437755957) * 10 ^ 70 +
        9203098614624584834318276278827325655367551438164224918739799508151911) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (130 - x)) = _
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

theorem recurrence4A4Square_coeff_131 :
    recurrence4A4Square.coeff 131 =
      -(((4721809572096308525674762018219595694306063653 * 10 ^ 70 +
        9317797526973619909720440013776210844997749805018544684405360691347235) * 10 ^ 70 +
        3810736566876736645868142201898123149123109646870157193059162106658948) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (131 - x)) = _
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

theorem recurrence4A4Square_coeff_132 :
    recurrence4A4Square.coeff 132 =
      (((12245380980808774970811934617469185384299384231 * 10 ^ 70 +
        3547653041937712957108581027779498982031289874967014733517065683373307) * 10 ^ 70 +
        4831473941716684844268574032537280973314487679616296732357941981577749) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (132 - x)) = _
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

theorem recurrence4A4Square_coeff_133 :
    recurrence4A4Square.coeff 133 =
      -(((31148638734403906502628113311914357907419839591 * 10 ^ 70 +
        0010924342816463319918776249008329786479139516797199612549593769560275) * 10 ^ 70 +
        9141263765881934229059939903932527648585316031999288458393309500009028) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (133 - x)) = _
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

theorem recurrence4A4Square_coeff_134 :
    recurrence4A4Square.coeff 134 =
      (((77722444416709017441169896808424669185098572572 * 10 ^ 70 +
        2060364635212768924176945218992456615467048442990516179378945884572136) * 10 ^ 70 +
        4260768505397094906047618983947749520961909533777497032670739914239427) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (134 - x)) = _
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

theorem recurrence4A4Square_coeff_135 :
    recurrence4A4Square.coeff 135 =
      -(((190252766505959382408693403548234090826868173116 * 10 ^ 70 +
        8264471528589725400512593420802855152878686404605036208628762657565737) * 10 ^ 70 +
        2862962972796265110995444015024190718718370017671200114859513539581754) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (135 - x)) = _
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

theorem recurrence4A4Square_coeff_136 :
    recurrence4A4Square.coeff 136 =
      (((456907294360938763443100234061656748882704848489 * 10 ^ 70 +
        0751493926274368296985849759020286646464043091594200173451715185577218) * 10 ^ 70 +
        4830160831559495689514480844430767763979586109778117724070594222863034) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (136 - x)) = _
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

theorem recurrence4A4Square_coeff_137 :
    recurrence4A4Square.coeff 137 =
      -(((1076643993704583677851088142572549245486350109402 * 10 ^ 70 +
        9831294125047671693179098730018844053621113032916320227562700998070868) * 10 ^ 70 +
        6502641517815811306342869756733926252830457161097321456702221229927446) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (137 - x)) = _
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

theorem recurrence4A4Square_coeff_138 :
    recurrence4A4Square.coeff 138 =
      (((2489409466607374341443467012416756401653526210231 * 10 ^ 70 +
        4923704469054431466193797996538942607084174437997476225730888020575058) * 10 ^ 70 +
        3991848530901806451230164591051438098482085800081456545251145448983090) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (138 - x)) = _
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

theorem recurrence4A4Square_coeff_139 :
    recurrence4A4Square.coeff 139 =
      -(((5648497543184008379525920617929465471016328060250 * 10 ^ 70 +
        7252048055945060120042255115400159603869404884838726253178712515825523) * 10 ^ 70 +
        3484489276980894197941703324194138506265540118770793458643736440493668) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (139 - x)) = _
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

theorem recurrence4A4Square_coeff_140 :
    recurrence4A4Square.coeff 140 =
      (((12578044105099352385171764260834292499369031477065 * 10 ^ 70 +
        4349817055732352028987500226819165451060443146473053296665538886028170) * 10 ^ 70 +
        4111192611623542641712376125955219680775003331768429361621503785525889) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (140 - x)) = _
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

theorem recurrence4A4Square_coeff_141 :
    recurrence4A4Square.coeff 141 =
      -(((27489509437162762786731787726698171688208231531277 * 10 ^ 70 +
        3776089390472489519088748628713649423754225166502499545239129205263837) * 10 ^ 70 +
        6810942512910692419902608689651148331393319820322771346914264881253802) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (141 - x)) = _
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

theorem recurrence4A4Square_coeff_142 :
    recurrence4A4Square.coeff 142 =
      (((58968993074554401430096299118164546981466211655565 * 10 ^ 70 +
        3506298810403992445579497689803217091777346437626443975913989522778279) * 10 ^ 70 +
        0296719147310971776559141776686432918786624495506224630436528376969938) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (142 - x)) = _
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

theorem recurrence4A4Square_coeff_143 :
    recurrence4A4Square.coeff 143 =
      -(((124168497611773931341913520654010124485825217650403 * 10 ^ 70 +
        9064244943505790714088256353105198081842348340741837501812937511176585) * 10 ^ 70 +
        3051571059309356447657590261282360260680379356442644442770848157149018) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (143 - x)) = _
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

theorem recurrence4A4Square_coeff_144 :
    recurrence4A4Square.coeff 144 =
      (((256659474775194694143476002021568984033717095210282 * 10 ^ 70 +
        7920163399090856925838319331604729376502310134483766270032432397942205) * 10 ^ 70 +
        4038968906884971157064560062904359927750139324593860386522911403321125) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (144 - x)) = _
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

theorem recurrence4A4Square_coeff_145 :
    recurrence4A4Square.coeff 145 =
      -(((520819865900038236453359753632454680014121237853782 * 10 ^ 70 +
        0560218479704036083770269566416677939189315480072724435329957923896876) * 10 ^ 70 +
        9059214889744476186986811042061603027255069101836593269369775011193276) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (145 - x)) = _
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

theorem recurrence4A4Square_coeff_146 :
    recurrence4A4Square.coeff 146 =
      (((1037593880456711304616975349335301765107527661513103 * 10 ^ 70 +
        2384347627485168275684455966702911155954235987167772826767913032762811) * 10 ^ 70 +
        9121900121349952787705174520599136721630365485210556092830280209774667) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (146 - x)) = _
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

theorem recurrence4A4Square_coeff_147 :
    recurrence4A4Square.coeff 147 =
      -(((2029556751062258105822932369028884437433513000289994 * 10 ^ 70 +
        5806581796862441853750525763716777358138647435949606658550562841989420) * 10 ^ 70 +
        9921431928589130506860253274421261875136660440474224834233129853034050) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (147 - x)) = _
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

theorem recurrence4A4Square_coeff_148 :
    recurrence4A4Square.coeff 148 =
      (((3897914676281399686960899990669065239183630680539299 * 10 ^ 70 +
        7640821223119268648263239430401765671708132183381231584636248057524466) * 10 ^ 70 +
        8997604844915243273050774884883850638917696957339177515241234054672177) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (148 - x)) = _
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

theorem recurrence4A4Square_coeff_149 :
    recurrence4A4Square.coeff 149 =
      -(((7350946602560983597487550577607140054973683493067092 * 10 ^ 70 +
        1179718059487628871874131324715757316649113498067520266116037261805529) * 10 ^ 70 +
        8437459442178283982429756685230815224923818411545819727462827212525100) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (149 - x)) = _
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

theorem recurrence4A4Square_coeff_150 :
    recurrence4A4Square.coeff 150 =
      (((13613054962056286650629435548039232360682126110625936 * 10 ^ 70 +
        1938090543446556573496236773824006935498637183837713141680629693101749) * 10 ^ 70 +
        8847619428029310130588084969164091043273564268753217085612639429865423) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (150 - x)) = _
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

theorem recurrence4A4Square_coeff_151 :
    recurrence4A4Square.coeff 151 =
      -(((24756543433837161941111237251089989569578849829123863 * 10 ^ 70 +
        3333237179601244312573145734686737654603591072799717862020470128967693) * 10 ^ 70 +
        3350366283353160354505762886238536656508944478767928376133375883010076) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (151 - x)) = _
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

theorem recurrence4A4Square_coeff_152 :
    recurrence4A4Square.coeff 152 =
      (((44214661665395639689613886524611916690842026815189053 * 10 ^ 70 +
        8623143135686226438237953483048922749666540291644186480618600397403586) * 10 ^ 70 +
        2370591443714154428777814263945189463866818661968361030321572881664341) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (152 - x)) = _
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

theorem recurrence4A4Square_coeff_153 :
    recurrence4A4Square.coeff 153 =
      -(((77553862935789723426461232935124387766341074998827947 * 10 ^ 70 +
        3967356203435824751229105085603052033151650194868355468040235681022604) * 10 ^ 70 +
        8360851949812058801746143470477685982180431805917827254126972569177934) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (153 - x)) = _
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

theorem recurrence4A4Square_coeff_154 :
    recurrence4A4Square.coeff 154 =
      (((133604004239997743181925463519917954316779752905348491 * 10 ^ 70 +
        3202695738039366318512857980622861010823131245429932260755108105771222) * 10 ^ 70 +
        1473671352842445249412855371805181228461737102669775368573488996111116) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (154 - x)) = _
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

theorem recurrence4A4Square_coeff_155 :
    recurrence4A4Square.coeff 155 =
      -(((226064129470722424792510674253623380169234523670377031 * 10 ^ 70 +
        8550730252317765612462987678992920130547048074841312731881463333671787) * 10 ^ 70 +
        2658463749217420055363271930900658773786712217607609985439629404272324) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (155 - x)) = _
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

theorem recurrence4A4Square_coeff_156 :
    recurrence4A4Square.coeff 156 =
      (((375713128230057224490336055443358052216668998639243404 * 10 ^ 70 +
        3042335415623380132929938215580143333585537441905375446329757249650298) * 10 ^ 70 +
        7052035506706129579237858616482353581732283565434472591234436507171213) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (156 - x)) = _
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

theorem recurrence4A4Square_coeff_157 :
    recurrence4A4Square.coeff 157 =
      -(((613351135750687989117321412056376771304429778689329063 * 10 ^ 70 +
        9337565587929164833417794715656251167199327389175504324569414679046682) * 10 ^ 70 +
        9342684447938841244098374265978817602395082696260241429158075625346362) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (157 - x)) = _
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

theorem recurrence4A4Square_coeff_158 :
    recurrence4A4Square.coeff 158 =
      (((983568924890009997384442510795555512306924003403772376 * 10 ^ 70 +
        7914930081878629513848269702267942343867980293190781859851021387358175) * 10 ^ 70 +
        5537381954669417049312712820528896570290904962684090985404724333794238) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (158 - x)) = _
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

theorem recurrence4A4Square_coeff_159 :
    recurrence4A4Square.coeff 159 =
      -(((1549377205574492019042045753661207542795854405909322667 * 10 ^ 70 +
        4506453770502700216551554077134071530876669306784516238848378568180283) * 10 ^ 70 +
        5260688313258446339359266516664621492217958974247554609105182709996782) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (159 - x)) = _
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

theorem recurrence4A4Square_coeff_160 :
    recurrence4A4Square.coeff 160 =
      (((2397614576139228211493664763696786624707473581189847476 * 10 ^ 70 +
        5799849624340713816963271650582931556404131979536589562579743036175225) * 10 ^ 70 +
        5245942617185485498467067773050273300201232422432957499750292881568036) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (160 - x)) = _
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

theorem recurrence4A4Square_coeff_161 :
    recurrence4A4Square.coeff 161 =
      -(((3644884132020079043416321673331994132602705033836165263 * 10 ^ 70 +
        6300121079619921114043495948752651765331918031821555500728455027093419) * 10 ^ 70 +
        1980978322902138107058878554261528969058377877047574804042756761792222) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (161 - x)) = _
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

theorem recurrence4A4Square_coeff_162 :
    recurrence4A4Square.coeff 162 =
      (((5443544046271666360608902159098243477739808934493862109 * 10 ^ 70 +
        2303330289518620717088474399923609131377844445401688235076785659050281) * 10 ^ 70 +
        8465486447317185576651342235639559484969601782210337692708670215100027) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (162 - x)) = _
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

theorem recurrence4A4Square_coeff_163 :
    recurrence4A4Square.coeff 163 =
      -(((7987008242103645963749311733125018024252311487408627468 * 10 ^ 70 +
        8265264658583330289362538730105021664224322197049944364922302810196738) * 10 ^ 70 +
        6103025617152651343684228902771396898576683069981504739000577891684782) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (163 - x)) = _
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

theorem recurrence4A4Square_coeff_164 :
    recurrence4A4Square.coeff 164 =
      (((11513326922956313947033515190776923544693665536898008066 * 10 ^ 70 +
        3870622364939914304738065050316565608628067849288478456190346571017135) * 10 ^ 70 +
        8173981011422384740754458215512286325337393774216696933935377667704748) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (164 - x)) = _
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

theorem recurrence4A4Square_coeff_165 :
    recurrence4A4Square.coeff 165 =
      -(((16305758729489339144784383612141978238992512818406211920 * 10 ^ 70 +
        1974316246943728648324944443207094841926184445633122977926152959416008) * 10 ^ 70 +
        6376848095206852549989984157127043067537491945814150744071052461677850) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (165 - x)) = _
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

theorem recurrence4A4Square_coeff_166 :
    recurrence4A4Square.coeff 166 =
      (((22688879267686860141898986220007830093490354607755358166 * 10 ^ 70 +
        8007998418475322710832213520759221920740299210311818169466935239223750) * 10 ^ 70 +
        1313491809892261041867780212981536113961498956205142351874351611699178) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (166 - x)) = _
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

theorem recurrence4A4Square_coeff_167 :
    recurrence4A4Square.coeff 167 =
      -(((31018768517923557242637002993976237884466726853249663720 * 10 ^ 70 +
        4328917292568414406421383267424211210927719282015077047457670271589953) * 10 ^ 70 +
        9260216690212470163277747902724496907182595324847399268502691927306956) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (167 - x)) = _
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

theorem recurrence4A4Square_coeff_168 :
    recurrence4A4Square.coeff 168 =
      (((41666055753444141409891377690820591585973483223132225159 * 10 ^ 70 +
        6944989113640153187840913829231821215606498519364661506437617799053473) * 10 ^ 70 +
        1631342100398570289433050019958036355946351300053700420146132903687342) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (168 - x)) = _
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

theorem recurrence4A4Square_coeff_169 :
    recurrence4A4Square.coeff 169 =
      -(((54991131778316616130147179840578408723516289455059798838 * 10 ^ 70 +
        2491977193598665460955257730797438397094309827179725534407811098268231) * 10 ^ 70 +
        0498463632469328628581827149733834182184246208029522821510963348818188) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (169 - x)) = _
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
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_170 :
    recurrence4A4Square.coeff 170 =
      (((71311684777118168972469672652878866293112455432926783581 * 10 ^ 70 +
        3728169750004797491962697999843191426401722461301002199327838536342588) * 10 ^ 70 +
        5075936554530186250475725388072447403029498596945512310165686136793644) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (170 - x)) = _
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
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_171 :
    recurrence4A4Square.coeff 171 =
      -(((90863842818953149225682384252812941183362311683410575524 * 10 ^ 70 +
        5519937488096363253393616566102916336324502798293086228965116770771874) * 10 ^ 70 +
        7163635769465411253329701777724416685241969527201585696676575799192248) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (171 - x)) = _
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_172 :
    recurrence4A4Square.coeff 172 =
      (((113759509968405632148179210427780613181098891152445898304 * 10 ^ 70 +
        1742591082847119553590493876344077309683654898273590273961045517387115) * 10 ^ 70 +
        6599685110470604620329026907050117602674948990896425028658887482665504) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (172 - x)) = _
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_173 :
    recurrence4A4Square.coeff 173 =
      -(((139943791505062232844368949209907097226440399351760025241 * 10 ^ 70 +
        8582434457709716965483730100935058319666641763310538221523719545120739) * 10 ^ 70 +
        0777769393695600014481161259628700754256420119308202404766914414112244) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (173 - x)) = _
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_174 :
    recurrence4A4Square.coeff 174 =
      (((169157489441048120816101239446191157229112347221408483250 * 10 ^ 70 +
        3697054009297957519154247090781587214672333216279180164943846934603234) * 10 ^ 70 +
        2379783306976159120183544468335496546535377564918906259905630094506416) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (174 - x)) = _
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_175 :
    recurrence4A4Square.coeff 175 =
      -(((200910261541479122978263994878898205238334755480186218655 * 10 ^ 70 +
        4403070129495884692939436244497950837323830418924566759382574106163058) * 10 ^ 70 +
        1655123389072886078544337432631306573414486021140487142589393579781622) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (175 - x)) = _
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_176 :
    recurrence4A4Square.coeff 176 =
      (((234469947483307010792583609477740439270726132438831567924 * 10 ^ 70 +
        1556985751779363215943666917215135568056166742852197943002654388054321) * 10 ^ 70 +
        4599159755768155904176536313223892610408120204120589731722409068697946) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (176 - x)) = _
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_177 :
    recurrence4A4Square.coeff 177 =
      -(((268872623031898976694755990744938881320110903044378211246 * 10 ^ 70 +
        1717747836097915009010986821276099468217838749794759512884189798951117) * 10 ^ 70 +
        7903666672148586433631684052279059655674918256686892653137686390061182) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (177 - x)) = _
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4A4Square_coeff_178 :
    recurrence4A4Square.coeff 178 =
      (((302956121296265715235405604388833002748452345531534964354 * 10 ^ 70 +
        1583772919738127824596869978222953110118839822761632626553120599482847) * 10 ^ 70 +
        7221273240889637731586594579691954302318974272959759175039896413223536) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (178 - x)) = _
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (179 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_179 :
    recurrence4A4Square.coeff 179 =
      -(((335417191595079335783426495993733858282663438246096963618 * 10 ^ 70 +
        9245548196579066785378767448025345071209330388570229482542484067757334) * 10 ^ 70 +
        6754168586836844548816738386479855238052326034094236959998436117312310) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (179 - x)) = _
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
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (180 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (180 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_180 :
    recurrence4A4Square.coeff 180 =
      (((364889445935595588127778226556197747992916579990507181992 * 10 ^ 70 +
        0155157968281824950271380045525718896008395591243372434629126814509730) * 10 ^ 70 +
        1416636805779186244324208538085233365481594132853852392342715507802426) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (180 - x)) = _
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
    rw [show 19 = 17 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (181 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (181 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_181 :
    recurrence4A4Square.coeff 181 =
      -(((390036196869353763699375104828793122379655538642745281878 * 10 ^ 70 +
        5764190620635005577342473456644392551884481671008259419379767426645783) * 10 ^ 70 +
        8567024984539692398859739712045208225513882404210645156627301892310326) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (181 - x)) = _
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
    rw [show 19 = 16 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (182 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (182 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_182 :
    recurrence4A4Square.coeff 182 =
      (((409649711880739028934204303560564737670602740524565687651 * 10 ^ 70 +
        2674092066107389491448590997692071568666379736663681117796326079788308) * 10 ^ 70 +
        6738777562007860511138105251988172829465636660969886328024306709295631) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (182 - x)) = _
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
    rw [show 19 = 15 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (183 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_183 :
    recurrence4A4Square.coeff 183 =
      -(((422746770411582793389201425312733717363928457383588656520 * 10 ^ 70 +
        8563115521943428032215668811959204880553903183075208734628445978984787) * 10 ^ 70 +
        4714667974035909919925700123351675836383922010928261298194778588933740) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (183 - x)) = _
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
    rw [show 19 = 14 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (184 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_184 :
    recurrence4A4Square.coeff 184 =
      (((428650065522276463701204830429357589939076007943086726674 * 10 ^ 70 +
        9517082736975542038740678984156082776842721343499772745689681165490047) * 10 ^ 70 +
        0986479937542070486259211742675675426788510321949576921307272431047380) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (184 - x)) = _
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
    rw [show 19 = 13 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (185 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_185 :
    recurrence4A4Square.coeff 185 =
      -(((427046101246395825590689270159520357403031420306069981024 * 10 ^ 70 +
        2404045644313236304050586421977875136476729292816473686402708965047837) * 10 ^ 70 +
        2358405295703182647212180528360124181080306112147951454612015927943084) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (185 - x)) = _
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
    rw [show 19 = 12 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (186 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_186 :
    recurrence4A4Square.coeff 186 =
      (((418012713579035398656406837399545159213685379028800105881 * 10 ^ 70 +
        0573043378037156460763877649021941778563234905535031595313910373661106) * 10 ^ 70 +
        9550831061193223386083379575976995792565383295702990848881812434668914) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (186 - x)) = _
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
    rw [show 19 = 11 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (187 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_187 :
    recurrence4A4Square.coeff 187 =
      -(((402012860082047760077834425387693313101317980388448299299 * 10 ^ 70 +
        8248750239925089045538968805326449410704860059228917138934678224525407) * 10 ^ 70 +
        7681640844510851563329380488555362774340677207358475557948493552970212) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (187 - x)) = _
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
    rhs
    rw [show 19 = 10 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (188 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_188 :
    recurrence4A4Square.coeff 188 =
      (((379855361764639814868774632597611954391606058747143626934 * 10 ^ 70 +
        9134229371815264139989493451200183841919261620314483570216767095025299) * 10 ^ 70 +
        1943284564366756845737814851135769065370509685434712328331043251439314) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (188 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (189 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_189 :
    recurrence4A4Square.coeff 189 =
      -(((352627224344112058833064197867527899329811709830901650004 * 10 ^ 70 +
        0429178705801982359290940643522738108516331135384702503139137347836167) * 10 ^ 70 +
        3296156587544902908715820036167254021694322009813308814520932050515204) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (189 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 8 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (190 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_190 :
    recurrence4A4Square.coeff 190 =
      (((321605413274647149330150240458141247854441728113719832717 * 10 ^ 70 +
        8369363029256315482242558810801402024801627685447936758473774396741428) * 10 ^ 70 +
        4625928630795363015699345199335017392457471549276417421347603121203316) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (190 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 7 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (191 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_191 :
    recurrence4A4Square.coeff 191 =
      -(((288158034220106430055545520947246978491622560600922626775 * 10 ^ 70 +
        3293637295374103543012839853674581312791010455165484029592460902541929) * 10 ^ 70 +
        0092504357120275270745142458396075988692583908505266638448455001819938) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (191 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 6 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (192 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_192 :
    recurrence4A4Square.coeff 192 =
      (((253645515155670428821528993759992467496785290024952004519 * 10 ^ 70 +
        0838507393764447853442853728171040953831993587991183076824569677780794) * 10 ^ 70 +
        6168771320087229645517206485004641437333247027760157635088927403332371) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (192 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (193 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_193 :
    recurrence4A4Square.coeff 193 =
      -(((219331585529996803506930266222367925793192036311821557426 * 10 ^ 70 +
        9362255143411226401453693267658757778821652230648636140651353026990416) * 10 ^ 70 +
        7242163051305740772679773979373445859556903934349752063136196590984210) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (193 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (194 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_194 :
    recurrence4A4Square.coeff 194 =
      (((186311827670682026624166658136892876353430733663949858630 * 10 ^ 70 +
        4494055147848451640516762877928860288819313715970733845301390386972743) * 10 ^ 70 +
        0759978687420081503163177224832344008107082038074965450923467902626372) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (194 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (195 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_195 :
    recurrence4A4Square.coeff 195 =
      -(((155464741962837488812586687621201157480021822867450682578 * 10 ^ 70 +
        2488101330879698442746027115673006546637988778676654712462175465165993) * 10 ^ 70 +
        4544325407678509775665733024487058393867305959041687234755984963198008) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (195 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (196 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_196 :
    recurrence4A4Square.coeff 196 =
      (((127427118392381065839882942502466480902928369947614812521 * 10 ^ 70 +
        2525045415556483503440165459271310478864521136766148059755988597402841) * 10 ^ 70 +
        9985327621110617581311324948884611502340632170715492947642455215258325) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (196 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (197 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_197 :
    recurrence4A4Square.coeff 197 =
      -(((102592535404833112151688276304999575971011934128250194615 * 10 ^ 70 +
        6980643493219230456178813150841591836591013021986682418608629238495081) * 10 ^ 70 +
        9218508075084922943352625785658448232462475568690465232130015007472774) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (197 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (198 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_198 :
    recurrence4A4Square.coeff 198 =
      (((81129414085277207201028988260946296401492233132327530885 * 10 ^ 70 +
        1078904800542346886430369846904832920280036119803873953523983474818778) * 10 ^ 70 +
        9467940692156947978614397365074641762601940321118164817285484678148371) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (198 - x)) = _
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
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (199 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_199 :
    recurrence4A4Square.coeff 199 =
      -(((63013494108596073565776899025629335254722917631687407692 * 10 ^ 70 +
        0845175065262546844550611429259315733769189221582649618470053692114422) * 10 ^ 70 +
        7198765024080990449602820235423760093409228880333214649113776232041146) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (199 - x)) = _
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
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (200 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_200 :
    recurrence4A4Square.coeff 200 =
      (((48068950334476905191384537113348402133256915480667362455 * 10 ^ 70 +
        5444151627424178861576880004165486766861280428989611884721315136099516) * 10 ^ 70 +
        3385717429800055397868243836028985166158530449411624008579025175875980) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (200 - x)) = _
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
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (201 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_201 :
    recurrence4A4Square.coeff 201 =
      -(((36012561551805236600548148108189611122453257228700005083 * 10 ^ 70 +
        5693938968212015225651646296228725888941361787708449076639880209290048) * 10 ^ 70 +
        5252726426439809536446457263444762429549559277054193979421739169400704) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (201 - x)) = _
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
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (202 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_202 :
    recurrence4A4Square.coeff 202 =
      (((26496185958463573779905569020754419634294307955309527545 * 10 ^ 70 +
        5855086086492875453641366270022544273785889090247636645640473422874710) * 10 ^ 70 +
        5561614090556906450286813214936724965363941253255684044431636703494868) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (202 - x)) = _
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (203 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_203 :
    recurrence4A4Square.coeff 203 =
      -(((19144040059705333728485452663903582169458974156736493316 * 10 ^ 70 +
        8458314321074021489978833455535826920804889287321798556868735531739077) * 10 ^ 70 +
        8608033885100865747896538408359493215962733525712715492231818925036336) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (203 - x)) = _
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
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (204 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_204 :
    recurrence4A4Square.coeff 204 =
      (((13582660458167184482803590411430919284119998468196418364 * 10 ^ 70 +
        8198004884283256334352882746879601408420443820818665712271017112909344) * 10 ^ 70 +
        5963474725973716565159863142386940885978283988010059448595012953394438) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (204 - x)) = _
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
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (205 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_205 :
    recurrence4A4Square.coeff 205 =
      -(((9462730703731137754127840100113519611698308675726303114 * 10 ^ 70 +
        6387889143553735731400601293070638214788161559305188052231179204481268) * 10 ^ 70 +
        9028709583365712202382056818867469521989553786061643145935841798938136) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (205 - x)) = _
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
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (206 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_206 :
    recurrence4A4Square.coeff 206 =
      (((6473022365620740490254318320939731146410833105855250611 * 10 ^ 70 +
        4279500360995181172032432447846045877010117583133817282536276920187993) * 10 ^ 70 +
        8248608441691702804631000138258744008362794259941571316075465471596449) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (206 - x)) = _
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (207 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_207 :
    recurrence4A4Square.coeff 207 =
      -(((4347449753806361752010689588855252196257447609203421700 * 10 ^ 70 +
        7717394731910403500971533080953207209378199820054861410945949992658184) * 10 ^ 70 +
        6639158202685679092161201831511659694497866307324395231054985672536998) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (207 - x)) = _
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (208 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_208 :
    recurrence4A4Square.coeff 208 =
      (((2866658605224515369856653543771671471471783336477337948 * 10 ^ 70 +
        0635016525919137980213195554045269426571932309037986482318078843235327) * 10 ^ 70 +
        8361632020628334925136972081174136984382540594718955985291530151858513) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (208 - x)) = _
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
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (209 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_209 :
    recurrence4A4Square.coeff 209 =
      -(((1855699707196045286063010442444333693214423179250532999 * 10 ^ 70 +
        8292901910844455952974862918281945861833184856309874389133513491419345) * 10 ^ 70 +
        9205939998040725607675995455042560543540550692770543856143145054793180) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (209 - x)) = _
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
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (210 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_210 :
    recurrence4A4Square.coeff 210 =
      (((1179248760178926450798875731022362979052245898446067790 * 10 ^ 70 +
        9911929648889563074493524196474404911374628368772726427566452998669486) * 10 ^ 70 +
        9852040994003639503495152469162559977475329918129814051453435088021544) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (210 - x)) = _
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
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (211 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_211 :
    recurrence4A4Square.coeff 211 =
      -(((735604187053004512340435901195117717494977086241298009 * 10 ^ 70 +
        7401683216177114509750095822773533059233603101112406799065292110239850) * 10 ^ 70 +
        2826540141460840037615953299446168767208222761851851482578621373388644) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (211 - x)) = _
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
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (212 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_212 :
    recurrence4A4Square.coeff 212 =
      (((450400040136300826309160521923469593211558472577584070 * 10 ^ 70 +
        2051930018430684261907085130096312651873092556026490048762380579738644) * 10 ^ 70 +
        0654599245132779998507092215312684002621615448829107384526095738881235) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (212 - x)) = _
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
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (213 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_213 :
    recurrence4A4Square.coeff 213 =
      -(((270671175717443746072336484750044567380720928171180963 * 10 ^ 70 +
        0468597266612986213027248037043989867620064942390462098883184636891982) * 10 ^ 70 +
        1286744151662268279992957668900813150099767939640742342984444148396796) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (213 - x)) = _
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (214 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_214 :
    recurrence4A4Square.coeff 214 =
      (((159642461282754684879883767022115737944804460831916416 * 10 ^ 70 +
        7608720532190604865637322801650119821319554576423448922221628479255075) * 10 ^ 70 +
        3918980439273235065741788997452261580470836532114885311318462836497570) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (214 - x)) = _
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (215 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_215 :
    recurrence4A4Square.coeff 215 =
      -(((92403998491850340090970333697297715317577459778934754 * 10 ^ 70 +
        3784293180952922783042307775278221618185188901649702842296816464395107) * 10 ^ 70 +
        8413668469958181877160443930082107427672819522653567725301334012348876) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (215 - x)) = _
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
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (216 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_216 :
    recurrence4A4Square.coeff 216 =
      (((52485821083020052899656749584683283422396683777882284 * 10 ^ 70 +
        1333006131220269825548200746774059591240638255145250539840696090199284) * 10 ^ 70 +
        1582707327746218519737370256563756241619320620312822998058592053999607) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (216 - x)) = _
  rw [show 217 = 38 +
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
  rw [recurrence4A4Square_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (217 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_217 :
    recurrence4A4Square.coeff 217 =
      -(((29253310714650046896634953636701788323309795934458929 * 10 ^ 70 +
        1135771744235423675965157680158947148913108098171772088271850180922739) * 10 ^ 70 +
        5945480791297925771682844346149732883771094412365956774516726738020950) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (217 - x)) = _
  rw [show 218 = 39 +
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
  rw [recurrence4A4Square_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (218 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_218 :
    recurrence4A4Square.coeff 218 =
      (((15997898512680883402591305114788000415854192083059761 * 10 ^ 70 +
        0195177051089515462202280556037680418378361377328524415342553609238374) * 10 ^ 70 +
        8164159332818843428165054534885809080638268291588808357195540868298550) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (218 - x)) = _
  rw [show 219 = 40 +
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
  rw [recurrence4A4Square_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (219 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_219 :
    recurrence4A4Square.coeff 219 =
      -(((8583792619237343730583067348609113878611103912040421 * 10 ^ 70 +
        5479625774138231589878861941200905213201627633915821313984844539671799) * 10 ^ 70 +
        9267345741054540617061320858354100467072997659446205824944969495796896) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (219 - x)) = _
  rw [show 220 = 41 +
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
  rw [recurrence4A4Square_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (220 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_220 :
    recurrence4A4Square.coeff 220 =
      (((4518538367919438756059288031304001532105093119995733 * 10 ^ 70 +
        2850429024651360562486354583694137581676873872487880670331989441062541) * 10 ^ 70 +
        3012743899885908797557561409375095840083849018214583107317337411395945) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (220 - x)) = _
  rw [show 221 = 42 +
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
  rw [recurrence4A4Square_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4A4Square_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (221 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_221 :
    recurrence4A4Square.coeff 221 =
      -(((2333426858926108274126654916171416754239382641026936 * 10 ^ 70 +
        2901056149826979382694512123751182952007201716806848136229476256015520) * 10 ^ 70 +
        1309361448291461190543526772043600880516808853851340752365320968192068) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (221 - x)) = _
  rw [show 222 = 43 +
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
  rw [recurrence4A4Square_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
