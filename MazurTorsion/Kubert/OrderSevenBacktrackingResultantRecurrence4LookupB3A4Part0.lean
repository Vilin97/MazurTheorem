/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3A4 coefficient convolution

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
  recurrence4B3_coeff_0
  recurrence4B3_coeff_1
  recurrence4B3_coeff_10
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109

attribute [local simp]
  recurrence4B3_coeff_11
  recurrence4B3_coeff_110
  recurrence4B3_coeff_111
  recurrence4B3_coeff_112
  recurrence4B3_coeff_113
  recurrence4B3_coeff_114
  recurrence4B3_coeff_115
  recurrence4B3_coeff_116
  recurrence4B3_coeff_117
  recurrence4B3_coeff_118
  recurrence4B3_coeff_119
  recurrence4B3_coeff_12
  recurrence4B3_coeff_120
  recurrence4B3_coeff_121
  recurrence4B3_coeff_122
  recurrence4B3_coeff_123
  recurrence4B3_coeff_124
  recurrence4B3_coeff_125
  recurrence4B3_coeff_126
  recurrence4B3_coeff_127
  recurrence4B3_coeff_128
  recurrence4B3_coeff_129
  recurrence4B3_coeff_13
  recurrence4B3_coeff_130
  recurrence4B3_coeff_131
  recurrence4B3_coeff_132
  recurrence4B3_coeff_133
  recurrence4B3_coeff_134
  recurrence4B3_coeff_135
  recurrence4B3_coeff_136
  recurrence4B3_coeff_137
  recurrence4B3_coeff_138
  recurrence4B3_coeff_139
  recurrence4B3_coeff_14
  recurrence4B3_coeff_140
  recurrence4B3_coeff_141
  recurrence4B3_coeff_142
  recurrence4B3_coeff_143
  recurrence4B3_coeff_144
  recurrence4B3_coeff_145
  recurrence4B3_coeff_146
  recurrence4B3_coeff_147
  recurrence4B3_coeff_148
  recurrence4B3_coeff_149
  recurrence4B3_coeff_15
  recurrence4B3_coeff_150
  recurrence4B3_coeff_151
  recurrence4B3_coeff_152
  recurrence4B3_coeff_153
  recurrence4B3_coeff_154
  recurrence4B3_coeff_155
  recurrence4B3_coeff_156
  recurrence4B3_coeff_157
  recurrence4B3_coeff_158
  recurrence4B3_coeff_159
  recurrence4B3_coeff_16
  recurrence4B3_coeff_160
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163
  recurrence4B3_coeff_164
  recurrence4B3_coeff_17
  recurrence4B3_coeff_18
  recurrence4B3_coeff_19

attribute [local simp]
  recurrence4B3_coeff_2
  recurrence4B3_coeff_20
  recurrence4B3_coeff_21
  recurrence4B3_coeff_22
  recurrence4B3_coeff_23
  recurrence4B3_coeff_24
  recurrence4B3_coeff_25
  recurrence4B3_coeff_26
  recurrence4B3_coeff_27
  recurrence4B3_coeff_28
  recurrence4B3_coeff_29
  recurrence4B3_coeff_3
  recurrence4B3_coeff_30
  recurrence4B3_coeff_31
  recurrence4B3_coeff_32
  recurrence4B3_coeff_33
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
  recurrence4B3_coeff_4
  recurrence4B3_coeff_40
  recurrence4B3_coeff_41
  recurrence4B3_coeff_42
  recurrence4B3_coeff_43
  recurrence4B3_coeff_44
  recurrence4B3_coeff_45
  recurrence4B3_coeff_46
  recurrence4B3_coeff_47
  recurrence4B3_coeff_48
  recurrence4B3_coeff_49
  recurrence4B3_coeff_5
  recurrence4B3_coeff_50
  recurrence4B3_coeff_51
  recurrence4B3_coeff_52
  recurrence4B3_coeff_53
  recurrence4B3_coeff_54
  recurrence4B3_coeff_55
  recurrence4B3_coeff_56
  recurrence4B3_coeff_57
  recurrence4B3_coeff_58
  recurrence4B3_coeff_59
  recurrence4B3_coeff_6
  recurrence4B3_coeff_60
  recurrence4B3_coeff_61
  recurrence4B3_coeff_62
  recurrence4B3_coeff_63
  recurrence4B3_coeff_64
  recurrence4B3_coeff_65
  recurrence4B3_coeff_66
  recurrence4B3_coeff_67
  recurrence4B3_coeff_68
  recurrence4B3_coeff_69
  recurrence4B3_coeff_7
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77

attribute [local simp]
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
  recurrence4B3_coeff_8
  recurrence4B3_coeff_80
  recurrence4B3_coeff_81
  recurrence4B3_coeff_82
  recurrence4B3_coeff_83
  recurrence4B3_coeff_84
  recurrence4B3_coeff_85
  recurrence4B3_coeff_86
  recurrence4B3_coeff_87
  recurrence4B3_coeff_88
  recurrence4B3_coeff_89
  recurrence4B3_coeff_9
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

theorem recurrence4B3A4_coeff_0 :
    recurrence4B3A4.coeff 0 =
      (-17170333563205017326343168 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_1 :
    recurrence4B3A4.coeff 1 =
      (63765286811474699076992674944 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_2 :
    recurrence4B3A4.coeff 2 =
      (-51558851730324849482796682197792 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_3 :
    recurrence4B3A4.coeff 3 =
      (-75682887295544516468778111016532136 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_4 :
    recurrence4B3A4.coeff 4 =
      (169503547611494126153709633557401566284 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_5 :
    recurrence4B3A4.coeff 5 =
      (-110545608536465323112602061600564415166728 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_6 :
    recurrence4B3A4.coeff 6 =
      (30391720998073691699717733756473548080821198 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_7 :
    recurrence4B3A4.coeff 7 =
      (-9262104637886248654636690882910874797137953054 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_8 :
    recurrence4B3A4.coeff 8 =
      (5145575856698294529205511969328677367811025869980 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_9 :
    recurrence4B3A4.coeff 9 =
      (-1086046462413650888054133701416983597870976383994900 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_10 :
    recurrence4B3A4.coeff 10 =
      (-626600649901033956763947088477199642203949036411582270 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_11 :
    recurrence4B3A4.coeff 11 =
      (514198754912965874274195752204557015896411457380322470971 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_12 :
    recurrence4B3A4.coeff 12 =
      (-170245807094603034138188199416580583734359065939032374569663 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_13 :
    recurrence4B3A4.coeff 13 =
      (30935033518289031514104127673384094796758667528666789954565219 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_14 :
    recurrence4B3A4.coeff 14 =
      (-2622062958699295268566392295929843595782015088896367945335413019 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_15 :
    recurrence4B3A4.coeff 15 =
      (2948582024453440676599997047928135638629698250642125473794668839 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_16 :
    recurrence4B3A4.coeff 16 =
      (-68530268170995041534988187931086504765669973835226124400684314243244 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_17 :
    recurrence4B3A4.coeff 17 =
      ((6 * 10 ^ 70 +
        1002931404494411823583227494502255114532846138999548347733471659552715) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_18 :
    recurrence4B3A4.coeff 18 =
      -((2408 * 10 ^ 70 +
        1834275356176856670375706754654700974873630705651664880766817152090355) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_19 :
    recurrence4B3A4.coeff 19 =
      ((668003 * 10 ^ 70 +
        3100365237488501639556065127333452195269520300088583822032477789463014) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_20 :
    recurrence4B3A4.coeff 20 =
      -((147423907 * 10 ^ 70 +
        2219909680397463209859047986731475926781373117813391762412974955647626) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_21 :
    recurrence4B3A4.coeff 21 =
      ((27062320657 * 10 ^ 70 +
        1518789458551453282066098105151009392405662385050293109062143103849542) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_22 :
    recurrence4B3A4.coeff 22 =
      -((4194195608754 * 10 ^ 70 +
        1221167322610049029016789386730496850536211848162824960777672524318434) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_23 :
    recurrence4B3A4.coeff 23 =
      ((548500713518168 * 10 ^ 70 +
        0461194092393600195268921087289640960707561005926787805585484703806091) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_24 :
    recurrence4B3A4.coeff 24 =
      -((59529386384730404 * 10 ^ 70 +
        8728758346280526533414526710753425906921166890618442671909436852521305) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_25 :
    recurrence4B3A4.coeff 25 =
      ((5092116171534792667 * 10 ^ 70 +
        1568043175578299590467719939764472607873989387564482408198907072297270) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_26 :
    recurrence4B3A4.coeff 26 =
      -((283380160846016553060 * 10 ^ 70 +
        5603905858643695775631297132244047214282361717208146166569701468523954) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_27 :
    recurrence4B3A4.coeff 27 =
      -((3331046813802695265472 * 10 ^ 70 +
        7629008268487652290252961928164585785044542866111086406000721923375628) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_28 :
    recurrence4B3A4.coeff 28 =
      ((3546246969183283327850324 * 10 ^ 70 +
        3991675643711748510219912074308064193056029674625844172810868981078656) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_29 :
    recurrence4B3A4.coeff 29 =
      -((595571730118155461468567904 * 10 ^ 70 +
        1739621766949171952780314997481529698944353670032640190778803508658434) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_30 :
    recurrence4B3A4.coeff 30 =
      ((70757612577922893895446693135 * 10 ^ 70 +
        7563266110419335394315068064873374648986734487172948687944901602555596) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_31 :
    recurrence4B3A4.coeff 31 =
      -((6912653328665081957274875041917 * 10 ^ 70 +
        3959126273426882982903848818683961051869177695950759645980819336406331) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4B3A4_coeff_32 :
    recurrence4B3A4.coeff 32 =
      ((584624022135074751031264439738414 * 10 ^ 70 +
        7219324874820497787158067345885579157904988081176490020932307358075662) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (32 - x)) = _
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

theorem recurrence4B3A4_coeff_33 :
    recurrence4B3A4.coeff 33 =
      -((43874037860933431831248717406825486 * 10 ^ 70 +
        5486017903424476004937673759585406965650844202142876299160484029534237) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (33 - x)) = _
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

theorem recurrence4B3A4_coeff_34 :
    recurrence4B3A4.coeff 34 =
      ((2963910064216881476950357323491138200 * 10 ^ 70 +
        6430641651574506596721178817245415665030802146408736609995806752675673) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (34 - x)) = _
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

theorem recurrence4B3A4_coeff_35 :
    recurrence4B3A4.coeff 35 =
      -((181937754015303410527269542639558718178 * 10 ^ 70 +
        1836028794213912347083773384707439782783709731934123865659480615074017) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (35 - x)) = _
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

theorem recurrence4B3A4_coeff_36 :
    recurrence4B3A4.coeff 36 =
      ((10215915213600439366270322595190986243881 * 10 ^ 70 +
        1991469047372949327619478921475545975063917068304174488144580720768729) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (36 - x)) = _
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

theorem recurrence4B3A4_coeff_37 :
    recurrence4B3A4.coeff 37 =
      -((527365847793271567731341771763966848940532 * 10 ^ 70 +
        7614608500999034617012475841845086211702114063820725244327904739003969) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (37 - x)) = _
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

theorem recurrence4B3A4_coeff_38 :
    recurrence4B3A4.coeff 38 =
      ((25127111427606667387433163851521921716320358 * 10 ^ 70 +
        1903154542521475625540246735253770726115653092010327526007355907677114) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (38 - x)) = _
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

theorem recurrence4B3A4_coeff_39 :
    recurrence4B3A4.coeff 39 =
      -((1108547341908187973571276171236303651934134748 * 10 ^ 70 +
        4141197333678674989303728195461118405345633430584838054971700947002019) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (39 - x)) = _
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

theorem recurrence4B3A4_coeff_40 :
    recurrence4B3A4.coeff 40 =
      ((45402826512917426964002354106900213186420188613 * 10 ^ 70 +
        8598407465738301604389048732712524000347777277561396753679056094547287) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (40 - x)) = _
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

theorem recurrence4B3A4_coeff_41 :
    recurrence4B3A4.coeff 41 =
      -((1730066051280948636054755388538318068191254015382 * 10 ^ 70 +
        7669725739740949522023085017042111380765774113850576079003713088899872) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (41 - x)) = _
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

theorem recurrence4B3A4_coeff_42 :
    recurrence4B3A4.coeff 42 =
      ((61440186868523226076847677074433156749983792476551 * 10 ^ 70 +
        5236230984800485691547342265054235471144111913457935732645203011638376) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (42 - x)) = _
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

theorem recurrence4B3A4_coeff_43 :
    recurrence4B3A4.coeff 43 =
      -((2036322918751745348648828387025486323298850604107719 * 10 ^ 70 +
        6691068851520591657372871392985630233510231512384377164541717684802739) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (43 - x)) = _
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

theorem recurrence4B3A4_coeff_44 :
    recurrence4B3A4.coeff 44 =
      ((63047988248638330402200374744283793246456029282308472 * 10 ^ 70 +
        5871217202603437280566052153487678772603245394091316072123106889109522) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (44 - x)) = _
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

theorem recurrence4B3A4_coeff_45 :
    recurrence4B3A4.coeff 45 =
      -((1824592192401261495827628789319637660417700282855900683 * 10 ^ 70 +
        2880924151867233459882780993043580115426617327158882717188052908359317) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (45 - x)) = _
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

theorem recurrence4B3A4_coeff_46 :
    recurrence4B3A4.coeff 46 =
      ((49356520548113354178724953368019327534039062282588353164 * 10 ^ 70 +
        3213570781338789948958714722176608240496008895387214866476756821383914) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (46 - x)) = _
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

theorem recurrence4B3A4_coeff_47 :
    recurrence4B3A4.coeff 47 =
      -((1247173142215588937376198593673987860619045555483565554523 * 10 ^ 70 +
        9550145810461779281230599062930574357952678828737037868970809180791729) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (47 - x)) = _
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

theorem recurrence4B3A4_coeff_48 :
    recurrence4B3A4.coeff 48 =
      ((29391068774499547487033152468693243383540568327934365177097 * 10 ^ 70 +
        6428589388634073721929235600119956775274594652633314911551548489276782) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (48 - x)) = _
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

theorem recurrence4B3A4_coeff_49 :
    recurrence4B3A4.coeff 49 =
      -((643988556587790952350133673332682823755147252680104054510622 * 10 ^ 70 +
        5422529391215386448274914396354701124396089306426871715610034319224975) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (49 - x)) = _
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

theorem recurrence4B3A4_coeff_50 :
    recurrence4B3A4.coeff 50 =
      ((13047588943244749795115690222515983803989450520251425446497161 * 10 ^ 70 +
        9425307701547514776238969044198095065865640483978778284046407655652874) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (50 - x)) = _
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

theorem recurrence4B3A4_coeff_51 :
    recurrence4B3A4.coeff 51 =
      -((242026927414999306503619473438532509080966421650465781823986494 * 10 ^ 70 +
        9634296327264320394299766025954353995334609163736951949048596070950728) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (51 - x)) = _
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

theorem recurrence4B3A4_coeff_52 :
    recurrence4B3A4.coeff 52 =
      ((4032513029095859205120214678873334849892986199526067413683207099 * 10 ^ 70 +
        5218718916076043792159039889266861560023211639451273587223152398312916) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (52 - x)) = _
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

theorem recurrence4B3A4_coeff_53 :
    recurrence4B3A4.coeff 53 =
      -((57855105986179784351285160574356682828235167024002674046201340017 * 10 ^ 70 +
        9158825859408875410638575063199904116599652858562749518005163783537050) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (53 - x)) = _
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

theorem recurrence4B3A4_coeff_54 :
    recurrence4B3A4.coeff 54 =
      ((632083386135718499165264351008713347889428192977090362259980347761 * 10 ^ 70 +
        3690126671281390578030114213747596842684274100878746508193191573935024) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (54 - x)) = _
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

theorem recurrence4B3A4_coeff_55 :
    recurrence4B3A4.coeff 55 =
      -((2223775553871885018221969875564856471179025879078691750478719377731 * 10 ^ 70 +
        0166478563218233295385965577337149293331869861853423495702061468946228) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (55 - x)) = _
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

theorem recurrence4B3A4_coeff_56 :
    recurrence4B3A4.coeff 56 =
      -((135703096157525107000577293520594833110916780354964055485760070812149 * 10 ^ 70 +
        4019597140279954151563141638783854684293299058061822723520310539258057) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (56 - x)) = _
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

theorem recurrence4B3A4_coeff_57 :
    recurrence4B3A4.coeff 57 =
      ((5384944106712872961319107947397531570696695201594187511661262535135320 * 10 ^ 70 +
        3575509766377436047619903948610966975569422929162509988261744287804941) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (57 - x)) = _
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

theorem recurrence4B3A4_coeff_58 :
    recurrence4B3A4.coeff 58 =
      -(((13 * 10 ^ 70 +
        9352130086286857918425526675384713831970545053000563959241964430165651) * 10 ^ 70 +
        4901075895292370469312193972734570973846727231624029806301635567679093) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (58 - x)) = _
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

theorem recurrence4B3A4_coeff_59 :
    recurrence4B3A4.coeff 59 =
      (((300 * 10 ^ 70 +
        4777473268899604458112719800899014658692862783649596836959059828237189) * 10 ^ 70 +
        8851578618131351276975796594171539539887077379228654732997714634169059) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (59 - x)) = _
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

theorem recurrence4B3A4_coeff_60 :
    recurrence4B3A4.coeff 60 =
      -(((5774 * 10 ^ 70 +
        9694281347015255806191707762258361789481777231063335491468033099579213) * 10 ^ 70 +
        5141700998448042635920766444284782262860640809901405985969910544848421) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (60 - x)) = _
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

theorem recurrence4B3A4_coeff_61 :
    recurrence4B3A4.coeff 61 =
      (((101816 * 10 ^ 70 +
        9548949629205894015822444106852185598026771393789158126075468671872966) * 10 ^ 70 +
        6990501404511659116699881223102824336046401315941834632744482044942788) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (61 - x)) = _
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

theorem recurrence4B3A4_coeff_62 :
    recurrence4B3A4.coeff 62 =
      -(((1671949 * 10 ^ 70 +
        8875182957688473418189303124960629640777792506040416366504297162517098) * 10 ^ 70 +
        4925661539143895323377363919704895362850710859819134295223769386485593) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (62 - x)) = _
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

theorem recurrence4B3A4_coeff_63 :
    recurrence4B3A4.coeff 63 =
      (((25807067 * 10 ^ 70 +
        7166260244071107639217437512894443641670200914029275749883322034154223) * 10 ^ 70 +
        4167314919620557979265261956875746796132058080411052969693555905325262) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (63 - x)) = _
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

theorem recurrence4B3A4_coeff_64 :
    recurrence4B3A4.coeff 64 =
      -(((376702280 * 10 ^ 70 +
        9360887242358579709629690947397663444223618363156250838592224267247797) * 10 ^ 70 +
        4853004562488281472043269516264234411440790400190167329339477466269671) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (64 - x)) = _
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

theorem recurrence4B3A4_coeff_65 :
    recurrence4B3A4.coeff 65 =
      (((5222363639 * 10 ^ 70 +
        6720383426657146571029757489200042406011373870269596922457233457074556) * 10 ^ 70 +
        2577297612753412173306704944022632715720916267844526307261285278722179) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (65 - x)) = _
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

theorem recurrence4B3A4_coeff_66 :
    recurrence4B3A4.coeff 66 =
      -(((68982654889 * 10 ^ 70 +
        1526411436634432137327857818356574750794410403304770770340591867167712) * 10 ^ 70 +
        6199361397967747612054300262991831957574632798704008044881177508381249) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (66 - x)) = _
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

theorem recurrence4B3A4_coeff_67 :
    recurrence4B3A4.coeff 67 =
      (((870372817881 * 10 ^ 70 +
        4317227382245145106371143413016017754177580892177429438483036175099546) * 10 ^ 70 +
        3973784285460947532876777706450254884267851140506439475402331040605175) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (67 - x)) = _
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

theorem recurrence4B3A4_coeff_68 :
    recurrence4B3A4.coeff 68 =
      -(((10510983803957 * 10 ^ 70 +
        7717761554655355688437270062012057964564880777534057230913814459185176) * 10 ^ 70 +
        8166281760306581528289264080517613941103016718203506865640434093814423) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (68 - x)) = _
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

theorem recurrence4B3A4_coeff_69 :
    recurrence4B3A4.coeff 69 =
      (((121698732186185 * 10 ^ 70 +
        5768749131266580557340877107243820162046740992781204097536667020986148) * 10 ^ 70 +
        4526265840360259456976832740996878587344054667454641735840615492123990) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (69 - x)) = _
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

theorem recurrence4B3A4_coeff_70 :
    recurrence4B3A4.coeff 70 =
      -(((1352872417155737 * 10 ^ 70 +
        3541710841790632223220102055987649926821032292736216965124036423239098) * 10 ^ 70 +
        6236511725828860344880656241026003154907516563052067245956047545583579) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (70 - x)) = _
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

theorem recurrence4B3A4_coeff_71 :
    recurrence4B3A4.coeff 71 =
      (((14457635121594877 * 10 ^ 70 +
        6572835309633227328862718243022572241944242201348593587915025569612147) * 10 ^ 70 +
        9019342143908748280414798962045614673552314127913639986707182021765101) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (71 - x)) = _
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

theorem recurrence4B3A4_coeff_72 :
    recurrence4B3A4.coeff 72 =
      -(((148691246999517090 * 10 ^ 70 +
        6325446837146302679200900157713513509981958891836911183209108480849538) * 10 ^ 70 +
        3486650454007652885327669629627998806012697233676633567995803315834903) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (72 - x)) = _
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

theorem recurrence4B3A4_coeff_73 :
    recurrence4B3A4.coeff 73 =
      (((1473157400544504215 * 10 ^ 70 +
        5825894580398806062731264851661119180331475671120259179993657148442286) * 10 ^ 70 +
        7682139468261677168559733923692936424518012769854089751791257393053207) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (73 - x)) = _
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

theorem recurrence4B3A4_coeff_74 :
    recurrence4B3A4.coeff 74 =
      -(((14072647871657198398 * 10 ^ 70 +
        6013372398718816766000226524851234315961160261900981329530536647988718) * 10 ^ 70 +
        6707241075974446876920381689511250604112059777855260635414770139183299) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (74 - x)) = _
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

theorem recurrence4B3A4_coeff_75 :
    recurrence4B3A4.coeff 75 =
      (((129723713127066712106 * 10 ^ 70 +
        9062045138046107763169938828749465738172220509001559834162152192682568) * 10 ^ 70 +
        2378373484630940613603597446860070802150467429081419710052930895006801) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (75 - x)) = _
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

theorem recurrence4B3A4_coeff_76 :
    recurrence4B3A4.coeff 76 =
      -(((1154797632143634932093 * 10 ^ 70 +
        5155626549489875616090185028338133778562146118711874504844988367101959) * 10 ^ 70 +
        6714113598847748300093212856103453329899041173571017525800281705329516) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (76 - x)) = _
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

theorem recurrence4B3A4_coeff_77 :
    recurrence4B3A4.coeff 77 =
      (((9934312066601556428473 * 10 ^ 70 +
        6166902520341484000278420033070392472023156538768991182166075152996829) * 10 ^ 70 +
        2894374888165318454797636733753676281961107358147885539019813092450692) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (77 - x)) = _
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

theorem recurrence4B3A4_coeff_78 :
    recurrence4B3A4.coeff 78 =
      -(((82641316354142442822558 * 10 ^ 70 +
        1287636543387656009506541315954581432377075184054555223792009478497653) * 10 ^ 70 +
        9707138973917185391118235077046214832654892614296131590578455626803690) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (78 - x)) = _
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

theorem recurrence4B3A4_coeff_79 :
    recurrence4B3A4.coeff 79 =
      (((665194428897354010847527 * 10 ^ 70 +
        4375354593708784300533347337640658569770469600286197882352543570245864) * 10 ^ 70 +
        0220481095146071645637310637427004413811341121619887047159142038126733) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (79 - x)) = _
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

theorem recurrence4B3A4_coeff_80 :
    recurrence4B3A4.coeff 80 =
      -(((5183711416588398742482058 * 10 ^ 70 +
        4161399241109448812639153602108898032806530978577157754600184917315477) * 10 ^ 70 +
        5483134989119299255906256184623769527400629754661798506507151598184659) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (80 - x)) = _
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

theorem recurrence4B3A4_coeff_81 :
    recurrence4B3A4.coeff 81 =
      (((39129918108810769511461026 * 10 ^ 70 +
        3534342625856128924159970898462654208034640561423899933487935339583535) * 10 ^ 70 +
        4203771173875366010270915326764233076009035317206978586865259709862245) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (81 - x)) = _
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

theorem recurrence4B3A4_coeff_82 :
    recurrence4B3A4.coeff 82 =
      -(((286269888581612041018482754 * 10 ^ 70 +
        2798284241419195450336983731677527685216453669649508603925508406663260) * 10 ^ 70 +
        6527849581744393639678585318537483918676982813010872748387536675351702) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (82 - x)) = _
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

theorem recurrence4B3A4_coeff_83 :
    recurrence4B3A4.coeff 83 =
      (((2030731549190134173353717483 * 10 ^ 70 +
        6027492328822619222496384090525918964435522102669346753237413634839098) * 10 ^ 70 +
        4168650434525085400196247335179656609187910815950075456502851216175084) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (83 - x)) = _
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

theorem recurrence4B3A4_coeff_84 :
    recurrence4B3A4.coeff 84 =
      -(((13974645750143021023124748788 * 10 ^ 70 +
        3286080921903094504547107678824505371471194712593907405502112672720686) * 10 ^ 70 +
        1502082561935553247141282987229601610920392874971723168173437150225575) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (84 - x)) = _
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

theorem recurrence4B3A4_coeff_85 :
    recurrence4B3A4.coeff 85 =
      (((93332422697215245066981860640 * 10 ^ 70 +
        7175030302425972328797870280873306114698942961905151889863001386562495) * 10 ^ 70 +
        3301914419304692154534144550675247816551352448935702476289277250795186) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (85 - x)) = _
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

theorem recurrence4B3A4_coeff_86 :
    recurrence4B3A4.coeff 86 =
      -(((605216978608004026024019157748 * 10 ^ 70 +
        6767584652855674997209316354388003660667093661933482984215582364332933) * 10 ^ 70 +
        5024119061567527586002933850060040459299359286564293643750031175298635) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (86 - x)) = _
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

theorem recurrence4B3A4_coeff_87 :
    recurrence4B3A4.coeff 87 =
      (((3811991427867887295613167220477 * 10 ^ 70 +
        1641558926444311041264307743145014224055965668819727704593266963474604) * 10 ^ 70 +
        7047320018044125191189776910599117677666371323537147821621022134251030) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (87 - x)) = _
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

theorem recurrence4B3A4_coeff_88 :
    recurrence4B3A4.coeff 88 =
      -(((23330441763145265977525743345501 * 10 ^ 70 +
        8542200976883141878649002919865635895393684585171568450326578213367612) * 10 ^ 70 +
        8176162636868192589626047305330141407772016382566586170137018437619674) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (88 - x)) = _
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

theorem recurrence4B3A4_coeff_89 :
    recurrence4B3A4.coeff 89 =
      (((138798661393463720277650960024135 * 10 ^ 70 +
        0894413785469682673173376083417928982108878237956221949336976991296711) * 10 ^ 70 +
        1134086526310223973822682824847081748816923780940672475617725031608719) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (89 - x)) = _
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

theorem recurrence4B3A4_coeff_90 :
    recurrence4B3A4.coeff 90 =
      -(((802958988670632688315925877439129 * 10 ^ 70 +
        4707161317050025041788321177354585060206012999807194420896992200132526) * 10 ^ 70 +
        2841029413022391098325487507376066108048821874269716847100372579170091) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (90 - x)) = _
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

theorem recurrence4B3A4_coeff_91 :
    recurrence4B3A4.coeff 91 =
      (((4518513312190115216555419005517039 * 10 ^ 70 +
        4481001528764752933429775675822112665007113464202958286838365772727922) * 10 ^ 70 +
        2488667876217178593234615304532777316540806878823312140655419281257710) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (91 - x)) = _
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

theorem recurrence4B3A4_coeff_92 :
    recurrence4B3A4.coeff 92 =
      -(((24741977271544983482850845650847618 * 10 ^ 70 +
        2754094067242000904838386565559103780281222744534081936787630465101665) * 10 ^ 70 +
        3725398908525832496711437852926691523462732057533869428980634361693257) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (92 - x)) = _
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

theorem recurrence4B3A4_coeff_93 :
    recurrence4B3A4.coeff 93 =
      (((131870262798273360999468618575713771 * 10 ^ 70 +
        0468048417495254750686016604581443079678206354688997676479300095184238) * 10 ^ 70 +
        5694460597626085531035424761072100200480790653346484581844856213313050) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (93 - x)) = _
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

theorem recurrence4B3A4_coeff_94 :
    recurrence4B3A4.coeff 94 =
      -(((684328631877491941266550401624416059 * 10 ^ 70 +
        1857355193697270347138901508731900966944073954681682695068054806340237) * 10 ^ 70 +
        1295170635211820395974098727095582510377335202865565364450138590130390) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (94 - x)) = _
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

theorem recurrence4B3A4_coeff_95 :
    recurrence4B3A4.coeff 95 =
      (((3458714015603707433253391776253126520 * 10 ^ 70 +
        7427581444108431682410891743589867101558631732988612512276607457152266) * 10 ^ 70 +
        2503487788352919722627997100919830732333249925747254707532586066576621) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (95 - x)) = _
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

theorem recurrence4B3A4_coeff_96 :
    recurrence4B3A4.coeff 96 =
      -(((17030156874758781500537149009478620173 * 10 ^ 70 +
        2153473584353325573423331536294735828827874857289173582029117483466156) * 10 ^ 70 +
        5110852051178220331771600860911730011784058662304328585016188729795469) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (96 - x)) = _
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

theorem recurrence4B3A4_coeff_97 :
    recurrence4B3A4.coeff 97 =
      (((81713547659332573801131901327424935793 * 10 ^ 70 +
        4544409456415689762690124300307323893422090232738563001759469238494074) * 10 ^ 70 +
        3928167042330678094999574118368840426201371531124121338575169808178518) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (97 - x)) = _
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

theorem recurrence4B3A4_coeff_98 :
    recurrence4B3A4.coeff 98 =
      -(((382167622402274952655793593620425560104 * 10 ^ 70 +
        2023901886390645208715883143479953169203206583054353713888224009225752) * 10 ^ 70 +
        1972686216110604265577351141320652356043219240617534527327520591182237) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (98 - x)) = _
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

theorem recurrence4B3A4_coeff_99 :
    recurrence4B3A4.coeff 99 =
      (((1742636853986319585498385108308701423827 * 10 ^ 70 +
        8078167409585364930409492261083993315800340939204365786677377505351994) * 10 ^ 70 +
        3167878745873101143519529564279944149182528826710879452040515587461616) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (99 - x)) = _
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

theorem recurrence4B3A4_coeff_100 :
    recurrence4B3A4.coeff 100 =
      -(((7749216680790914686280124496095917371536 * 10 ^ 70 +
        3360875945395174161208873413465988278260363678138271120190378849481544) * 10 ^ 70 +
        9364205478576795016185339719666527080520600128150516324578108721604716) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (100 - x)) = _
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

theorem recurrence4B3A4_coeff_101 :
    recurrence4B3A4.coeff 101 =
      (((33613013865248194904233978005190680565279 * 10 ^ 70 +
        6726385135584595333347691601614142301193649629033599941368262786481337) * 10 ^ 70 +
        7122927320554046665892705679947331218351589570771068688876438012304379) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (101 - x)) = _
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

theorem recurrence4B3A4_coeff_102 :
    recurrence4B3A4.coeff 102 =
      -(((142250214170730300912113880164480969405766 * 10 ^ 70 +
        8965192764403260376681128764938094388221429130127149133512463197272179) * 10 ^ 70 +
        1886385678779145152889384591283589371338663327133882443417746678300517) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (102 - x)) = _
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

theorem recurrence4B3A4_coeff_103 :
    recurrence4B3A4.coeff 103 =
      (((587472712044569895745748529145431166662481 * 10 ^ 70 +
        8371393161703613914091425298129738480510390693886211314218947281712311) * 10 ^ 70 +
        9020208497875303814012071912879581900978833920810821271455309432759465) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (103 - x)) = _
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

theorem recurrence4B3A4_coeff_104 :
    recurrence4B3A4.coeff 104 =
      -(((2368109329715879970530890326605005856892301 * 10 ^ 70 +
        7824723249101909663336369580588269510086418819343710584201423688161799) * 10 ^ 70 +
        5546854674150492888410181955470446708766439293677647304684640772140597) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (104 - x)) = _
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

theorem recurrence4B3A4_coeff_105 :
    recurrence4B3A4.coeff 105 =
      (((9319265836621708516685148730914790047134524 * 10 ^ 70 +
        7223284158741298807988480090764915900830005820426667084721400395515878) * 10 ^ 70 +
        7047117160236274605431181831073656942444927222953897851216793617241238) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (105 - x)) = _
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

theorem recurrence4B3A4_coeff_106 :
    recurrence4B3A4.coeff 106 =
      -(((35810544445196143447253342977199648020939597 * 10 ^ 70 +
        9445952551271800942054376753122501666068741128041504680436915967882115) * 10 ^ 70 +
        0449482949183114002839387638802097456530838645480316885030338791312437) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (106 - x)) = _
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

theorem recurrence4B3A4_coeff_107 :
    recurrence4B3A4.coeff 107 =
      (((134390833889079997831996210951091083445757909 * 10 ^ 70 +
        5036060247688721279414587313517114548462510984291896453284247418825219) * 10 ^ 70 +
        9584338442374881244687163182931368486876743301612873475577837019549579) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (107 - x)) = _
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

theorem recurrence4B3A4_coeff_108 :
    recurrence4B3A4.coeff 108 =
      -(((492646120148494303572440690094176727647239581 * 10 ^ 70 +
        4163528024781812756371465693174136224066306170076086938556353841496615) * 10 ^ 70 +
        1601057645200646794729183948342598645009040090297731174162617788294284) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (108 - x)) = _
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

theorem recurrence4B3A4_coeff_109 :
    recurrence4B3A4.coeff 109 =
      (((1764336549448074964352811003197017348339900836 * 10 ^ 70 +
        6857595009064574384679937334680700011759136710343641057763162348634588) * 10 ^ 70 +
        8694431269154011769884610004995664887617098982870015861054343487555860) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (109 - x)) = _
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

theorem recurrence4B3A4_coeff_110 :
    recurrence4B3A4.coeff 110 =
      -(((6174192251027790269074647103418254242755169262 * 10 ^ 70 +
        8855995987720000435316531704805034181438764463421567781885233925686373) * 10 ^ 70 +
        7090017185369750638281745130077085405108475207009911406636027797656259) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (110 - x)) = _
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

theorem recurrence4B3A4_coeff_111 :
    recurrence4B3A4.coeff 111 =
      (((21115427103570884228113495172273541098494747766 * 10 ^ 70 +
        9967181924832148125611296783285708867402674228796854392419970694274813) * 10 ^ 70 +
        5697390351826732996267166217279482257765973990532255579566169312449264) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (111 - x)) = _
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

theorem recurrence4B3A4_coeff_112 :
    recurrence4B3A4.coeff 112 =
      -(((70584050509531498963686396818765890306341706776 * 10 ^ 70 +
        5383060019929926938196205771100053517590826241251243957029263731177477) * 10 ^ 70 +
        4320435635740612707210307807405347968851927469794701843933067807347477) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (112 - x)) = _
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

theorem recurrence4B3A4_coeff_113 :
    recurrence4B3A4.coeff 113 =
      (((230655416583564866894865005077581924688418614324 * 10 ^ 70 +
        3487579200889530642182882737114463956171954803556262344055585364789227) * 10 ^ 70 +
        8706406126720414304135033226370697758983238641292350592535220930098533) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (113 - x)) = _
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

theorem recurrence4B3A4_coeff_114 :
    recurrence4B3A4.coeff 114 =
      -(((736939759708285624128931794145404600620894373900 * 10 ^ 70 +
        7338720246324060413380854082799061755369269880032058200050367003722180) * 10 ^ 70 +
        8375874080830590821644125450631295317274712208624827583033188706632903) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (114 - x)) = _
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

theorem recurrence4B3A4_coeff_115 :
    recurrence4B3A4.coeff 115 =
      (((2302342885923350562128382457270753228855149918549 * 10 ^ 70 +
        4074374837464338739353615723875917246245839535288441099318889932720385) * 10 ^ 70 +
        2921436810429725267082702318928714894202631361789178834051048757257841) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (115 - x)) = _
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

theorem recurrence4B3A4_coeff_116 :
    recurrence4B3A4.coeff 116 =
      -(((7034508583790233436250436765452812938553584576717 * 10 ^ 70 +
        0414276939677117143935775415107419876124469934415989448177248930240400) * 10 ^ 70 +
        4581375845142440501397743265587736334069119977145084045153843798050042) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (116 - x)) = _
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

theorem recurrence4B3A4_coeff_117 :
    recurrence4B3A4.coeff 117 =
      (((21022144853406940940014413770586950761875226807956 * 10 ^ 70 +
        7454906630031133763953107711224509636611333706071742614186057431639037) * 10 ^ 70 +
        6886408486682357627171328272462214835503180923787569375931517548629774) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (117 - x)) = _
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

theorem recurrence4B3A4_coeff_118 :
    recurrence4B3A4.coeff 118 =
      -(((61454160567581157691180393802438281888335115269670 * 10 ^ 70 +
        2392563468550952832995273062117588129303641934248620525742402039785197) * 10 ^ 70 +
        3650396088096037776127834719248560646274408545703897077770704182543206) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (118 - x)) = _
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

theorem recurrence4B3A4_coeff_119 :
    recurrence4B3A4.coeff 119 =
      (((175754267774912529947952014183617856313289374201580 * 10 ^ 70 +
        7010488640174462364266331701263358390219642449959184703634910217702389) * 10 ^ 70 +
        6161292718921233774493193769012245092502682041644574208292181425010602) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (119 - x)) = _
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

theorem recurrence4B3A4_coeff_120 :
    recurrence4B3A4.coeff 120 =
      -(((491799371355712824103451204450138815550133818402891 * 10 ^ 70 +
        0065041957281442634414590735081396940746996484774946414475681030918808) * 10 ^ 70 +
        9350324413403999054054538807584083004453359925229186587793698472522968) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (120 - x)) = _
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

theorem recurrence4B3A4_coeff_121 :
    recurrence4B3A4.coeff 121 =
      (((1346612524695489303645537252266622193038070118320159 * 10 ^ 70 +
        4413256618738568179882354726221862132497222311096819476792088726171964) * 10 ^ 70 +
        0322428329092098878502501823042267401509268006485837922050490616689977) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (121 - x)) = _
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

theorem recurrence4B3A4_coeff_122 :
    recurrence4B3A4.coeff 122 =
      -(((3608385807721599677163618623982665042991241238938747 * 10 ^ 70 +
        8919098463820016219789892232014218659525851664254231106751071051494198) * 10 ^ 70 +
        4460133771437061868979613241112369718686141559837038024716068758968796) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (122 - x)) = _
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

theorem recurrence4B3A4_coeff_123 :
    recurrence4B3A4.coeff 123 =
      (((9463242325118584423929231941495792175189088169136342 * 10 ^ 70 +
        8974588414498170611185406171453696993608728162581662526338246986198179) * 10 ^ 70 +
        1784545229537896315330911009411940399413731339682367998795387819793559) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (123 - x)) = _
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

theorem recurrence4B3A4_coeff_124 :
    recurrence4B3A4.coeff 124 =
      -(((24291968559522735895760237822055211149907732512419015 * 10 ^ 70 +
        9566636065164176650958117514386729763064345439728500343145455353911430) * 10 ^ 70 +
        8239053183957475027604203716941816468561732187881681313454554140731404) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (124 - x)) = _
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

theorem recurrence4B3A4_coeff_125 :
    recurrence4B3A4.coeff 125 =
      (((61040538137429720670652180101765439776393062491870573 * 10 ^ 70 +
        5010190806683301594800683647639870130993563982784842108499817229703486) * 10 ^ 70 +
        8662709794247845157693865335023346187922638430825231787309263689657101) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (125 - x)) = _
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

theorem recurrence4B3A4_coeff_126 :
    recurrence4B3A4.coeff 126 =
      -(((150155804147401762533474392110651270863610823924651089 * 10 ^ 70 +
        0805032521715646128396047846663507614181888481404266928525276689211584) * 10 ^ 70 +
        2468849369721277643877913325146153464957543027401461527017990180982232) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (126 - x)) = _
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

theorem recurrence4B3A4_coeff_127 :
    recurrence4B3A4.coeff 127 =
      (((361632430189786388814737759861285147157728368515800074 * 10 ^ 70 +
        0479323605002208594899697060340432340359344071927314671781300528629628) * 10 ^ 70 +
        9946548316328345417473901839963855462110248407739740332671125114036916) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (127 - x)) = _
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

theorem recurrence4B3A4_coeff_128 :
    recurrence4B3A4.coeff 128 =
      -(((852757549074992265752552683489937510795480015301072889 * 10 ^ 70 +
        0196900637922206865390341485781209382466937770686402248450650877830011) * 10 ^ 70 +
        0708715169410265523194076182663961975360321538421502828578344113996459) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (128 - x)) = _
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

theorem recurrence4B3A4_coeff_129 :
    recurrence4B3A4.coeff 129 =
      (((1969002924148515082760707911394063110052372209209140397 * 10 ^ 70 +
        8441271901494159641404072580023252521522236052030453112735213250600718) * 10 ^ 70 +
        3935137965533301714048188419776232847015846470905733790865399567250378) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (129 - x)) = _
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

theorem recurrence4B3A4_coeff_130 :
    recurrence4B3A4.coeff 130 =
      -(((4452024215655902033185727859031792085283210928538164955 * 10 ^ 70 +
        1654464911642969188314152274301122266728322399763308504025103903476665) * 10 ^ 70 +
        6211856701806811242445108833778358144945317571599355853109622603163023) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (130 - x)) = _
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

theorem recurrence4B3A4_coeff_131 :
    recurrence4B3A4.coeff 131 =
      (((9857913034310825191799353227558396710620027980524623139 * 10 ^ 70 +
        1659473453603247966877354853128058697190144446905911685676440398729494) * 10 ^ 70 +
        4834477273407334004167738082409693286600652581400012916616477951210621) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (131 - x)) = _
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

theorem recurrence4B3A4_coeff_132 :
    recurrence4B3A4.coeff 132 =
      -(((21377299764247167481256870940918771738474691300169244439 * 10 ^ 70 +
        2252673691720319891735286978980918226133792276844284833919082805396210) * 10 ^ 70 +
        8162326875044309076564256258814709703699996298905408407657642472030210) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (132 - x)) = _
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

theorem recurrence4B3A4_coeff_133 :
    recurrence4B3A4.coeff 133 =
      (((45402874234782638786837117372811812682412759906624106672 * 10 ^ 70 +
        0858910423766075037769477028016262704430523556915532285500181873078245) * 10 ^ 70 +
        5845834242213978259776770286494177357387239981425606354711832187039912) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (133 - x)) = _
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

theorem recurrence4B3A4_coeff_134 :
    recurrence4B3A4.coeff 134 =
      -(((94448886410908939150886055173016015003170302209392779041 * 10 ^ 70 +
        3922640788802443409167708863152127269552499703997301358782095794528327) * 10 ^ 70 +
        1786897386150042172635335910636298473850373577457162738315093457778295) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (134 - x)) = _
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

theorem recurrence4B3A4_coeff_135 :
    recurrence4B3A4.coeff 135 =
      (((192447287289766088457059722583408653026320011705680205847 * 10 ^ 70 +
        2030534144042762091047575149571220545652776939002830431133389130066435) * 10 ^ 70 +
        3267659854828959774639417854520335974316313974372882926306376816340428) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (135 - x)) = _
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

theorem recurrence4B3A4_coeff_136 :
    recurrence4B3A4.coeff 136 =
      -(((384100376167951313646064619803193845498988202885407353668 * 10 ^ 70 +
        6457287204599078406597561740209816654959326873087627425443161585102185) * 10 ^ 70 +
        5684224645898090917994480414029601708208044160874165241960048308490589) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (136 - x)) = _
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

theorem recurrence4B3A4_coeff_137 :
    recurrence4B3A4.coeff 137 =
      (((750948604572307144691769344530925074037651128969233577994 * 10 ^ 70 +
        7386082103345173833665349101897879176421545983474381444541601801398802) * 10 ^ 70 +
        9275942153776105764825673728904686566473808300256608512483477713027732) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (137 - x)) = _
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

theorem recurrence4B3A4_coeff_138 :
    recurrence4B3A4.coeff 138 =
      -(((1438204924423884402018667195027573120218534761771823250689 * 10 ^ 70 +
        4532603732149509932515037072628214387377419460646431921840515664411486) * 10 ^ 70 +
        6217412318753103384847181253722337763434707812751597787267817387753161) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (138 - x)) = _
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

theorem recurrence4B3A4_coeff_139 :
    recurrence4B3A4.coeff 139 =
      (((2698278955469032066560068359080402345204249782679857384715 * 10 ^ 70 +
        7407843310518272159768694622544093697291412811331870170643347125073880) * 10 ^ 70 +
        8352318926058057760575383794731985771740904159665067973756429103075271) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (139 - x)) = _
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

theorem recurrence4B3A4_coeff_140 :
    recurrence4B3A4.coeff 140 =
      -(((4959258180494536380118547026653064451657354103445537849728 * 10 ^ 70 +
        0777651448445433985254097036208191729377238894675256431721382447780803) * 10 ^ 70 +
        8597123472055743819350647722181485746969487654439897385408471575596156) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (140 - x)) = _
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

theorem recurrence4B3A4_coeff_141 :
    recurrence4B3A4.coeff 141 =
      (((8929279428437885235883947042281531017948076558184847690865 * 10 ^ 70 +
        3491832989403583079072094108212846461427819570552236786601764382781520) * 10 ^ 70 +
        3506000862061470440122473144884494415718631928903258582378806600873588) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (141 - x)) = _
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

theorem recurrence4B3A4_coeff_142 :
    recurrence4B3A4.coeff 142 =
      -(((15750327849080757134399372382460340937766542409811712003977 * 10 ^ 70 +
        3868219363374500414391870031556341148612579676903720071958384011429140) * 10 ^ 70 +
        7193439093032175956854925775869839004345383572314961851535189604601031) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (142 - x)) = _
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

theorem recurrence4B3A4_coeff_143 :
    recurrence4B3A4.coeff 143 =
      (((27216824477247768428689410963615098107004517769708722959942 * 10 ^ 70 +
        8000018227574764075142406384262421644643286395398382017123551753557348) * 10 ^ 70 +
        6726729527820058815417167006586914692487842794877644140390267555927475) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (143 - x)) = _
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

theorem recurrence4B3A4_coeff_144 :
    recurrence4B3A4.coeff 144 =
      -(((46074276631110733022001841674826861344179775676098621120727 * 10 ^ 70 +
        2741108137999527831520399494608777886048865490308340630271305356807210) * 10 ^ 70 +
        2334186908118284558186596365931293381974892756672436346631011928278257) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (144 - x)) = _
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

theorem recurrence4B3A4_coeff_145 :
    recurrence4B3A4.coeff 145 =
      (((76409711833301157257165441584952152759542605872540778734886 * 10 ^ 70 +
        0641240162277608291650299597923667797057270373072027833883882574139153) * 10 ^ 70 +
        9361123383402443494334345278169611824143745800253797516301356045136530) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (145 - x)) = _
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

theorem recurrence4B3A4_coeff_146 :
    recurrence4B3A4.coeff 146 =
      -(((124136729688439167100386014451864937780875740626804540068861 * 10 ^ 70 +
        8829803206654840482833459803162481447091303514688187015645304486489616) * 10 ^ 70 +
        9371814814620534030458854377292589449106733147459830794361146801498220) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (146 - x)) = _
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

theorem recurrence4B3A4_coeff_147 :
    recurrence4B3A4.coeff 147 =
      (((197561918593097902883399650211606517503809407368430099239467 * 10 ^ 70 +
        3361612228964940198300955692991281782019883253453631441205397361109614) * 10 ^ 70 +
        4543367586305001114478478312773172708164290210564348247568794785420206) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (147 - x)) = _
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

theorem recurrence4B3A4_coeff_148 :
    recurrence4B3A4.coeff 148 =
      -(((307994768814111580325959285925804410574893054418016813012867 * 10 ^ 70 +
        8076830036353284822274819030278502519489277993793493634192100389382847) * 10 ^ 70 +
        7680113084262313059264053331341522315299555374351688534795317420168120) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (148 - x)) = _
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

theorem recurrence4B3A4_coeff_149 :
    recurrence4B3A4.coeff 149 =
      (((470330060882752567676811672514400045418069779055334438835821 * 10 ^ 70 +
        8438100373872585049509460593531070843107168939600603325925187254328925) * 10 ^ 70 +
        0712991148321636068798945006624420002531039091733005338490035552571482) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (149 - x)) = _
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

theorem recurrence4B3A4_coeff_150 :
    recurrence4B3A4.coeff 150 =
      -(((703492235409342256657528265731788603365992948946755188453610 * 10 ^ 70 +
        9524816303876879532446932695574317714432325819307818068263646115025217) * 10 ^ 70 +
        5447984110840511405001877591180947838985348852787663562298864860175864) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (150 - x)) = _
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

theorem recurrence4B3A4_coeff_151 :
    recurrence4B3A4.coeff 151 =
      (((1030590734034319962223536969471518204193099666436948264846654 * 10 ^ 70 +
        1493547198859372723558793214222562147522246119752021684662668649792904) * 10 ^ 70 +
        9101315254577119986581736971656574668852817110435447957427036214476857) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (151 - x)) = _
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

theorem recurrence4B3A4_coeff_152 :
    recurrence4B3A4.coeff 152 =
      -(((1478602510083843896773055183443005710969348371247735759149867 * 10 ^ 70 +
        3114094238989029313364649863607042246454607220726464284287085652784361) * 10 ^ 70 +
        1951946795638398553592103677144254248336013787287190909658808411325831) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (152 - x)) = _
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

theorem recurrence4B3A4_coeff_153 :
    recurrence4B3A4.coeff 153 =
      (((2077384742707583640066446616315974334012732085749752527418073 * 10 ^ 70 +
        7298831370498003069359773136880724579102753652080265391652547535740444) * 10 ^ 70 +
        2475169586896503019653084070010284906211965008094239824479981554370493) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (153 - x)) = _
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

theorem recurrence4B3A4_coeff_154 :
    recurrence4B3A4.coeff 154 =
      -(((2857840777596868752148933482032498780018124162722113846107679 * 10 ^ 70 +
        6307317397054848073542837969665984370779834928185172511635009427618526) * 10 ^ 70 +
        1745372183982786102221782766851229086711849639665742656791525651353672) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (154 - x)) = _
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

theorem recurrence4B3A4_coeff_155 :
    recurrence4B3A4.coeff 155 =
      (((3849127799237549498051064462399579676407802474216532753086808 * 10 ^ 70 +
        2577509098706399649827963163434937713816430505234862279047866758339925) * 10 ^ 70 +
        9701007123308605721052848368043167800620311602857218492293744720166974) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (155 - x)) = _
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

theorem recurrence4B3A4_coeff_156 :
    recurrence4B3A4.coeff 156 =
      -(((5074912928436252123788219607106846910329133324262684169926160 * 10 ^ 70 +
        8905501001099940579210386643106613828110236295697085462545778504339589) * 10 ^ 70 +
        3809348358973778726494822319302838172967727945663250528177172690427959) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (156 - x)) = _
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

theorem recurrence4B3A4_coeff_157 :
    recurrence4B3A4.coeff 157 =
      (((6548853039702880136488750152604631071483589088365115795159591 * 10 ^ 70 +
        6454752709071938742709257443576543074998739811146486457446397487062222) * 10 ^ 70 +
        9778501602300429846954484356558263938138954829186395245780853322923066) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (157 - x)) = _
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

theorem recurrence4B3A4_coeff_158 :
    recurrence4B3A4.coeff 158 =
      -(((8269677113438540007934052602976797502422919393563829182245989 * 10 ^ 70 +
        7719258584569908692915066990851712165925526356763381934407516939798792) * 10 ^ 70 +
        5501692389697944797071787755654521304930093555045225870059695707743916) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (158 - x)) = _
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

theorem recurrence4B3A4_coeff_159 :
    recurrence4B3A4.coeff 159 =
      (((10216458145899696982774632058299298509912354991192121288237897 * 10 ^ 70 +
        5052768994348837852375297346897726681381652099164707177965381193076964) * 10 ^ 70 +
        3594981460169681664127858996719008126146633852792633009654857007661377) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (159 - x)) = _
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

theorem recurrence4B3A4_coeff_160 :
    recurrence4B3A4.coeff 160 =
      -(((12344831550917946892194615972248162872147323282841714350270244 * 10 ^ 70 +
        8980715585125937228764514398376750174977609388385212247688071600616340) * 10 ^ 70 +
        3874988332707951894741988019648386010535157407428092796826789812211601) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (160 - x)) = _
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

theorem recurrence4B3A4_coeff_161 :
    recurrence4B3A4.coeff 161 =
      (((14584999183672579448841159655724427031230964983594281275844115 * 10 ^ 70 +
        1981061309955345199514596343913643392978461422323488808030958865311285) * 10 ^ 70 +
        1460197918880089084388394430786289419410958493573487745587140962437281) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (161 - x)) = _
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

theorem recurrence4B3A4_coeff_162 :
    recurrence4B3A4.coeff 162 =
      -(((16842307123780648306610760130741428707435689200691934555355420 * 10 ^ 70 +
        5791934062303947175338522089416385002441233537595399552405425762661010) * 10 ^ 70 +
        9313051952652711825381764972220193813138760585809697903019156525165366) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (162 - x)) = _
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

theorem recurrence4B3A4_coeff_163 :
    recurrence4B3A4.coeff 163 =
      (((19000972405436585999629831920289655571926152686985976071404138 * 10 ^ 70 +
        0023459363380074443544955979443616739060490037250860862406600713307891) * 10 ^ 70 +
        9739616444947985980736580897440749974037411841566874013365781669170917) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (163 - x)) = _
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

theorem recurrence4B3A4_coeff_164 :
    recurrence4B3A4.coeff 164 =
      -(((20931159090234489634482512021372387814601687830028977627790376 * 10 ^ 70 +
        0595596252551134190907292921214110461360852067712407511887774683837668) * 10 ^ 70 +
        6673608299309377925943703157365864768861762104600321774860568520170363) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (164 - x)) = _
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

private theorem recurrence4B3A4_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_165 :
    recurrence4B3A4.coeff 165 =
      (((22499104301971557945260780347955586289500113338053459774890747 * 10 ^ 70 +
        7039887138249154691531600427309310862591274144337612136423284518583795) * 10 ^ 70 +
        2394093070575716784337292103949982110469244910664582256841937456755881) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (165 - x)) = _
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
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (166 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_166 :
    recurrence4B3A4.coeff 166 =
      -(((23579443788258401959369290824566661655360133767591796624221243 * 10 ^ 70 +
        5142237752505462756675374046267723029157460344219951846054922317411023) * 10 ^ 70 +
        1133686576997973525036335032298979453465239036179396157386642065280219) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (166 - x)) = _
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
    rw [show 7 = 5 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (167 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_167 :
    recurrence4B3A4.coeff 167 =
      (((24068385163394137024956618559724896324674779374573030644190004 * 10 ^ 70 +
        3774777473287053284811647788674577485760392189314647652365293417845506) * 10 ^ 70 +
        9611456052823900898349696939949725992447427178519744444003465466824555) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (167 - x)) = _
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
    rw [show 8 = 5 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (168 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_168 :
    recurrence4B3A4.coeff 168 =
      -(((23896034504460385400952529177120406625670960057913486668354111 * 10 ^ 70 +
        8497839952193424224920478853561601223384098004310519764512492925887335) * 10 ^ 70 +
        1254989921390846308054987210833976639839023388842256227168176445261450) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (168 - x)) = _
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
    rw [show 9 = 5 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (169 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_169 :
    recurrence4B3A4.coeff 169 =
      (((23036091388248349785988231164416559877439160471177460948004837 * 10 ^ 70 +
        6569052499103959723105106594995835556552086516767167208918848258108508) * 10 ^ 70 +
        6160093144403251230401117303259922036564584358793419852822400359845212) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (169 - x)) = _
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
    rw [show 10 = 5 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (170 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_170 :
    recurrence4B3A4.coeff 170 =
      -(((21511340735374019009334576600711174564140105550809606632467019 * 10 ^ 70 +
        5553609305018784680523313926045337158944579491194341700825383453109628) * 10 ^ 70 +
        5195379040107518514674074165153391020125472559985893748136265098947715) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (170 - x)) = _
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
    rw [show 11 = 5 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (171 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_171 :
    recurrence4B3A4.coeff 171 =
      (((19393880030910731516542144540791406176397362440135304247692261 * 10 ^ 70 +
        3177287399581833314210275016439529203974480696067607587479421280901808) * 10 ^ 70 +
        1479914631825769812872948850723244094354092549986032178806314850743508) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (171 - x)) = _
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
    rw [show 12 = 5 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (172 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_172 :
    recurrence4B3A4.coeff 172 =
      -(((16799756516426785607689953908158390247720298512386738507799695 * 10 ^ 70 +
        7674442110890351113932254544211358427692055904261595142584216209173521) * 10 ^ 70 +
        6236251490723516700513310975418386723031617969500741212048212103362678) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (172 - x)) = _
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
    rw [show 13 = 5 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (173 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_173 :
    recurrence4B3A4.coeff 173 =
      (((13878525840095855670956590677030781536247897291756441823800699 * 10 ^ 70 +
        8266542153831944694710046972660871408270416950052066850249545593231495) * 10 ^ 70 +
        0662561260726034726801775888357966934479886184496381213032088231570722) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (173 - x)) = _
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
    rw [show 14 = 5 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (174 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_174 :
    recurrence4B3A4.coeff 174 =
      -(((10799027229890590178070150253455023268122914239943027358312887 * 10 ^ 70 +
        4280783773240980347861192873138997131581742422104048873815090222404449) * 10 ^ 70 +
        8142310328305428349761406423881090224184325761061164085255922279464249) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (174 - x)) = _
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
    rw [show 15 = 5 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (175 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_175 :
    recurrence4B3A4.coeff 175 =
      (((7733250619445091527417155152057236851488364915478360824521989 * 10 ^ 70 +
        6292526327142722478361708946470105509670913686652390022995524478454249) * 10 ^ 70 +
        9119307911009126089239705278784991548872838893501047228562632461295408) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (175 - x)) = _
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
    rw [show 16 = 5 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (176 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_176 :
    recurrence4B3A4.coeff 176 =
      -(((4840436715313507984118602285484020048323704479033852689060836 * 10 ^ 70 +
        8079002499308744240886802975935398630183246757331738539947078284326377) * 10 ^ 70 +
        2510817268048430025876511324337209049449184223925404903246141067645459) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (176 - x)) = _
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
    rw [show 17 = 5 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (177 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_177 :
    recurrence4B3A4.coeff 177 =
      (((2253454117332099240377821315012980953269052018004406370969841 * 10 ^ 70 +
        8467978586264847921898115660651505916768342799437809964915537671976892) * 10 ^ 70 +
        9674274815417825042884868792621217382222363910881310384106661328069654) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (177 - x)) = _
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
    rw [show 18 = 5 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (178 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_178 :
    recurrence4B3A4.coeff 178 =
      -(((69065062670329878692415453045003894120368514717753377175550 * 10 ^ 70 +
        9843853293229623308763645216812651017395623551115074037351527589844811) * 10 ^ 70 +
        8268245508698886272441180723567076819018143955225312165747954467124833) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (178 - x)) = _
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
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (179 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_179 :
    recurrence4B3A4.coeff 179 =
      -(((1656983134539141950940706486868244037773163916566868726077366 * 10 ^ 70 +
        7269696889329454832342709326322919564019867856682520287681558743743231) * 10 ^ 70 +
        1467841138476958779297439617754443105097676759791770119017656815301255) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (179 - x)) = _
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
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (180 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (180 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_180 :
    recurrence4B3A4.coeff 180 =
      (((2909882833696289064567522620008016879455974127586694662354384 * 10 ^ 70 +
        5064730375835693800974698120175560815915576196299954005167198995739922) * 10 ^ 70 +
        4196165511624937758269624152914401263593413632042353999609541702694185) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (180 - x)) = _
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
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (181 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (181 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_181 :
    recurrence4B3A4.coeff 181 =
      -(((3711283391408144823043890907902962610490703589940309056586189 * 10 ^ 70 +
        3230253967033708587923315134880497186577318088900915361740392909915364) * 10 ^ 70 +
        1225042068886190738456078687052392238524150272704187428821205161184860) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (181 - x)) = _
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
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (182 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (182 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_182 :
    recurrence4B3A4.coeff 182 =
      (((4111540086892461739981251831800459401430217025889851081678183 * 10 ^ 70 +
        4693695307305871639019345869773985233857549616670222111057329179607682) * 10 ^ 70 +
        2405225320958095384826824127045522265507529716185120771314593273586944) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (182 - x)) = _
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
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (183 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_183 :
    recurrence4B3A4.coeff 183 =
      -(((4180143858508476540858978507361311594826244345277641596311240 * 10 ^ 70 +
        0641818959349541219209518458530186536004694959663759479618022342150206) * 10 ^ 70 +
        3664145813826265744944030608338534521296853947342423676481703253044203) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (183 - x)) = _
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
  rw [recurrence4B3A4_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (184 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_184 :
    recurrence4B3A4.coeff 184 =
      (((3995816924820522537211226265839682699921957837883005710593366 * 10 ^ 70 +
        3858911078805868863432878931144161434317263267693006258359699396440768) * 10 ^ 70 +
        3943534384690300538572576325210653432021699901573773413380384144847087) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (184 - x)) = _
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
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (185 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_185 :
    recurrence4B3A4.coeff 185 =
      -(((3637554994176223764487902915643030931817138031346047444367038 * 10 ^ 70 +
        5046720310916804221523594856301078783615220374007231004201209203717982) * 10 ^ 70 +
        6366065446198122094303172896538850001480332741674881915479347559553231) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (185 - x)) = _
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
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (186 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_186 :
    recurrence4B3A4.coeff 186 =
      (((3177527061372675029112592537232894480896146250555795637816807 * 10 ^ 70 +
        4798615812600696153475482859900834916036709455710829156594911339383395) * 10 ^ 70 +
        2881658341991428123653352191424761615930022423850656443765135076973737) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (186 - x)) = _
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
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (187 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_187 :
    recurrence4B3A4.coeff 187 =
      -(((2676302418930648452781809475195484162609561825123449097881865 * 10 ^ 70 +
        6357669034280410612738959802667553099191980345307481550966647192736023) * 10 ^ 70 +
        4996517264711280953494278100439327495057689324055015718769260618624337) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (187 - x)) = _
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
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (188 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_188 :
    recurrence4B3A4.coeff 188 =
      (((2180451331058211141053987210843984178538410832164292291397024 * 10 ^ 70 +
        4467581584911962764290187519499064048040314188338237942304421964150338) * 10 ^ 70 +
        4352460408472028842956116364331291654691697792194005218963959859801864) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (188 - x)) = _
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (189 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_189 :
    recurrence4B3A4.coeff 189 =
      -(((1722229225596053738638075709445920709380571703348238685933114 * 10 ^ 70 +
        4599958109385506739917689943653705389180213395975309502164664068308667) * 10 ^ 70 +
        2739042997806692101115594167223470012468553686783408275453161343832882) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (189 - x)) = _
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
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (190 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_190 :
    recurrence4B3A4.coeff 190 =
      (((1320841728590254856233253737266523880283984573213591561840804 * 10 ^ 70 +
        5578444898238591514035341586819213528937557717487623390260807532727974) * 10 ^ 70 +
        7857792275732133725729145080030527917802653241966207015660017672516231) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (190 - x)) = _
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
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (191 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_191 :
    recurrence4B3A4.coeff 191 =
      -(((984705251410877097810170665628424516837962282567609617971127 * 10 ^ 70 +
        8022529597410387695630443218269727514257609544498621427393735543299868) * 10 ^ 70 +
        6658959826420785596275037844302927959510053471478889753490478405358374) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (191 - x)) = _
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
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (192 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_192 :
    recurrence4B3A4.coeff 192 =
      (((714145684126146521918844766032869231203187859436656429145310 * 10 ^ 70 +
        0023465742975566153461646714062887689131902689016353468014854729379367) * 10 ^ 70 +
        3790474021876462459045979284228976146311549980162305805166022530062218) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (192 - x)) = _
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (193 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_193 :
    recurrence4B3A4.coeff 193 =
      -(((504081512789996793217375976653160174143461002001018485259565 * 10 ^ 70 +
        3957720017433161111099175303125443874519184497137846436926687826691090) * 10 ^ 70 +
        4893224057688477823693448629441552363196932121888747106129974280572327) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (193 - x)) = _
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (194 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_194 :
    recurrence4B3A4.coeff 194 =
      (((346378571220193938768486041292234201317363596106488008205391 * 10 ^ 70 +
        9116724825822999540249629625091435066520519889326230126490795344511112) * 10 ^ 70 +
        7945504311934304221637129835606473555669420178592183769315727561092199) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (194 - x)) = _
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
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (195 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_195 :
    recurrence4B3A4.coeff 195 =
      -(((231707413191399880825985717789625451763145646191784547366928 * 10 ^ 70 +
        2631668668566468025735693021135499694876684488211649196777033821912757) * 10 ^ 70 +
        0586572266020341771102363167834672347095077519841581022937779134583594) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (195 - x)) = _
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
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (196 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_196 :
    recurrence4B3A4.coeff 196 =
      (((150856579718489913044813029858362015189311428900463560427222 * 10 ^ 70 +
        0126414543590588878115024417490523683241394912055663116539332829671007) * 10 ^ 70 +
        0413221257576309478377796571255117756089021820025088366788439502605124) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (196 - x)) = _
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
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (197 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_197 :
    recurrence4B3A4.coeff 197 =
      -(((95543019094774836853934989025377237940276505687894985567619 * 10 ^ 70 +
        5565611381939768751394219851828267899083101118462284159783826610587225) * 10 ^ 70 +
        2125678330702915102196443914189860752893604811087882274985830142255946) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (197 - x)) = _
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
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (198 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_198 :
    recurrence4B3A4.coeff 198 =
      (((58812074855794631734325199623534389286671219998707638108630 * 10 ^ 70 +
        5646408583802541942888179605306548572044466971801757442666874208622066) * 10 ^ 70 +
        9928129553965639809067727817228705228760348735688178866152254924967803) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (198 - x)) = _
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
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (199 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_199 :
    recurrence4B3A4.coeff 199 =
      -(((35138600088274906858679850136091915678461940089669326848877 * 10 ^ 70 +
        6324180382272201097342589689512645461687388872226799733445086767726408) * 10 ^ 70 +
        0423864248112521654883754075596200254263631297842759240599074652862356) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (199 - x)) = _
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (200 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_200 :
    recurrence4B3A4.coeff 200 =
      (((20336563367429645980705767828324404094317349173185313056688 * 10 ^ 70 +
        4973136070477178021307700458457005111914924403315209095559189698815951) * 10 ^ 70 +
        1332600817723987860302969586019259570178400834320535715869597855506083) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (200 - x)) = _
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (201 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_201 :
    recurrence4B3A4.coeff 201 =
      -(((11366495353273240915894251252602127609755405139871274618924 * 10 ^ 70 +
        0017378782493623633939340239665964183824090901440319715383801714625556) * 10 ^ 70 +
        5342393005135214772007781416179988740086706905859750288426417788799854) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (201 - x)) = _
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
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (202 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_202 :
    recurrence4B3A4.coeff 202 =
      (((6106540927608630249631005500769042713107190447748993220599 * 10 ^ 70 +
        8590906778975300138068001784354319971185231231826245698717165507190653) * 10 ^ 70 +
        7308980918325408693415339551878617825642748039427543399697946189007655) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (202 - x)) = _
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
    rw [show 51 = 13 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (203 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_203 :
    recurrence4B3A4.coeff 203 =
      -(((3129677075487442526739522860593903798181312967633968185800 * 10 ^ 70 +
        9767851529917139668478391223897545395352853478935381814118118535659206) * 10 ^ 70 +
        0447290170921129070301286897806585942936076909818553235961586964151156) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (203 - x)) = _
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
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (204 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_204 :
    recurrence4B3A4.coeff 204 =
      (((1510291615863271652745588967228798771702352528374504091010 * 10 ^ 70 +
        0386297740277753843676234220513239916496687497476749666542765445906219) * 10 ^ 70 +
        0546797136437315312697818607998355619391043469496245220074417804903562) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (204 - x)) = _
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
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (205 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_205 :
    recurrence4B3A4.coeff 205 =
      -(((669151369635943777137227279591927067428138744845602147236 * 10 ^ 70 +
        6278988363171026439733999398561714600295047333756952507593096267034920) * 10 ^ 70 +
        4754031671917475442055602563079619599715866311168312072135178698176035) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (205 - x)) = _
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
    rw [show 51 = 10 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (206 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_206 :
    recurrence4B3A4.coeff 206 =
      (((256718499677192076717525134096301269348565081267257180630 * 10 ^ 70 +
        0842495130264200929985569041795188301138543175889286988467221910271302) * 10 ^ 70 +
        2591630221781658401101264978192826397124205872771889431046434693668734) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (206 - x)) = _
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
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (207 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_207 :
    recurrence4B3A4.coeff 207 =
      -(((69891038407795409698015121984336367195362249305798518939 * 10 ^ 70 +
        2617507220029325565161355343346789296034895690354719930702655038729659) * 10 ^ 70 +
        9608586900182371864949750810740324806258613736158477095148866271368851) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (207 - x)) = _
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
    rw [show 51 = 8 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (208 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_208 :
    recurrence4B3A4.coeff 208 =
      -(((4644811418846471185475020929850689047343790350421460890 * 10 ^ 70 +
        9072143416509198543215886534074850676747997866585115811395635436139522) * 10 ^ 70 +
        8378961249441631079165677041594721651531930426076708835993211613325030) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (208 - x)) = _
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
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (209 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_209 :
    recurrence4B3A4.coeff 209 =
      (((27289912642454765826312633873342292917547730625619733898 * 10 ^ 70 +
        4033584147136267163038263415899593117142810857477950137015734780530124) * 10 ^ 70 +
        4856758249590434346985456121849394196256858780766555077078683971816303) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (209 - x)) = _
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
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (210 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_210 :
    recurrence4B3A4.coeff 210 =
      -(((28538662785557589200446352191530794082872199963341633507 * 10 ^ 70 +
        2530416888757232713771928930964847411744201702671173197061216227079737) * 10 ^ 70 +
        5418326981530225282155540262294953891603022902815591441848590929760152) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (210 - x)) = _
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
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (211 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_211 :
    recurrence4B3A4.coeff 211 =
      (((22740468722941059636481740304122389338558018118670063792 * 10 ^ 70 +
        6739297548187225322262873024342313256868189453795131262624095718159242) * 10 ^ 70 +
        8889134811778444195013634990379247945958255552260567683883866667574813) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (211 - x)) = _
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
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (212 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_212 :
    recurrence4B3A4.coeff 212 =
      -(((15982033767915420290951339770683992087420260362520967625 * 10 ^ 70 +
        8688680289144741422122537119680085731306020658880030544537587761165213) * 10 ^ 70 +
        7075326731465485423294173741174436209993435464230015113762246374955387) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (212 - x)) = _
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
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (213 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_213 :
    recurrence4B3A4.coeff 213 =
      (((10396708977828404146225380200698366691855309159576298242 * 10 ^ 70 +
        5106559213671476955529410806472048236705641154805546931169857950163551) * 10 ^ 70 +
        8969102711711199135123631246219244210132897744313617954707985937554406) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (213 - x)) = _
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
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (214 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_214 :
    recurrence4B3A4.coeff 214 =
      -(((6399004211506657593313676377347875038156418109631257623 * 10 ^ 70 +
        7216730879231001308318406526921995151161990010568096393430565551914900) * 10 ^ 70 +
        5770148811002709584707260745057022251037426621145702283260859575494289) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (214 - x)) = _
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
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
