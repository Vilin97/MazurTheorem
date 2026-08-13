/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3A3 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A3_coeff_0
  recurrence4A3_coeff_1
  recurrence4A3_coeff_10
  recurrence4A3_coeff_100
  recurrence4A3_coeff_101
  recurrence4A3_coeff_102
  recurrence4A3_coeff_103
  recurrence4A3_coeff_104
  recurrence4A3_coeff_105
  recurrence4A3_coeff_106
  recurrence4A3_coeff_107
  recurrence4A3_coeff_108
  recurrence4A3_coeff_109
  recurrence4A3_coeff_11
  recurrence4A3_coeff_110
  recurrence4A3_coeff_111
  recurrence4A3_coeff_112
  recurrence4A3_coeff_113
  recurrence4A3_coeff_114
  recurrence4A3_coeff_115
  recurrence4A3_coeff_116
  recurrence4A3_coeff_117
  recurrence4A3_coeff_118
  recurrence4A3_coeff_119
  recurrence4A3_coeff_12
  recurrence4A3_coeff_120
  recurrence4A3_coeff_121
  recurrence4A3_coeff_122
  recurrence4A3_coeff_123
  recurrence4A3_coeff_124
  recurrence4A3_coeff_125
  recurrence4A3_coeff_126
  recurrence4A3_coeff_127
  recurrence4A3_coeff_128
  recurrence4A3_coeff_129
  recurrence4A3_coeff_13
  recurrence4A3_coeff_130
  recurrence4A3_coeff_131
  recurrence4A3_coeff_132
  recurrence4A3_coeff_133
  recurrence4A3_coeff_134
  recurrence4A3_coeff_135
  recurrence4A3_coeff_136
  recurrence4A3_coeff_137
  recurrence4A3_coeff_138
  recurrence4A3_coeff_139
  recurrence4A3_coeff_14
  recurrence4A3_coeff_140
  recurrence4A3_coeff_141
  recurrence4A3_coeff_142
  recurrence4A3_coeff_143
  recurrence4A3_coeff_144
  recurrence4A3_coeff_145
  recurrence4A3_coeff_146
  recurrence4A3_coeff_147
  recurrence4A3_coeff_148
  recurrence4A3_coeff_149
  recurrence4A3_coeff_15
  recurrence4A3_coeff_150
  recurrence4A3_coeff_151
  recurrence4A3_coeff_152
  recurrence4A3_coeff_153
  recurrence4A3_coeff_154
  recurrence4A3_coeff_155

attribute [local simp]
  recurrence4A3_coeff_156
  recurrence4A3_coeff_157
  recurrence4A3_coeff_158
  recurrence4A3_coeff_159
  recurrence4A3_coeff_16
  recurrence4A3_coeff_160
  recurrence4A3_coeff_161
  recurrence4A3_coeff_162
  recurrence4A3_coeff_163
  recurrence4A3_coeff_164
  recurrence4A3_coeff_165
  recurrence4A3_coeff_166
  recurrence4A3_coeff_167
  recurrence4A3_coeff_168
  recurrence4A3_coeff_169
  recurrence4A3_coeff_17
  recurrence4A3_coeff_170
  recurrence4A3_coeff_171
  recurrence4A3_coeff_172
  recurrence4A3_coeff_173
  recurrence4A3_coeff_174
  recurrence4A3_coeff_175
  recurrence4A3_coeff_176
  recurrence4A3_coeff_177
  recurrence4A3_coeff_178
  recurrence4A3_coeff_179
  recurrence4A3_coeff_18
  recurrence4A3_coeff_180
  recurrence4A3_coeff_181
  recurrence4A3_coeff_182
  recurrence4A3_coeff_19
  recurrence4A3_coeff_2
  recurrence4A3_coeff_20
  recurrence4A3_coeff_21
  recurrence4A3_coeff_22
  recurrence4A3_coeff_23
  recurrence4A3_coeff_24
  recurrence4A3_coeff_25
  recurrence4A3_coeff_26
  recurrence4A3_coeff_27
  recurrence4A3_coeff_28
  recurrence4A3_coeff_29
  recurrence4A3_coeff_3
  recurrence4A3_coeff_30
  recurrence4A3_coeff_31
  recurrence4A3_coeff_32
  recurrence4A3_coeff_33
  recurrence4A3_coeff_34
  recurrence4A3_coeff_35
  recurrence4A3_coeff_36
  recurrence4A3_coeff_37
  recurrence4A3_coeff_38
  recurrence4A3_coeff_39
  recurrence4A3_coeff_4
  recurrence4A3_coeff_40
  recurrence4A3_coeff_41
  recurrence4A3_coeff_42
  recurrence4A3_coeff_43
  recurrence4A3_coeff_44
  recurrence4A3_coeff_45
  recurrence4A3_coeff_46
  recurrence4A3_coeff_47
  recurrence4A3_coeff_48
  recurrence4A3_coeff_49

attribute [local simp]
  recurrence4A3_coeff_5
  recurrence4A3_coeff_50
  recurrence4A3_coeff_51
  recurrence4A3_coeff_52
  recurrence4A3_coeff_53
  recurrence4A3_coeff_54
  recurrence4A3_coeff_55
  recurrence4A3_coeff_56
  recurrence4A3_coeff_57
  recurrence4A3_coeff_58
  recurrence4A3_coeff_59
  recurrence4A3_coeff_6
  recurrence4A3_coeff_60
  recurrence4A3_coeff_61
  recurrence4A3_coeff_62
  recurrence4A3_coeff_63
  recurrence4A3_coeff_64
  recurrence4A3_coeff_65
  recurrence4A3_coeff_66
  recurrence4A3_coeff_67
  recurrence4A3_coeff_68
  recurrence4A3_coeff_69
  recurrence4A3_coeff_7
  recurrence4A3_coeff_70
  recurrence4A3_coeff_71
  recurrence4A3_coeff_72
  recurrence4A3_coeff_73
  recurrence4A3_coeff_74
  recurrence4A3_coeff_75
  recurrence4A3_coeff_76
  recurrence4A3_coeff_77
  recurrence4A3_coeff_78
  recurrence4A3_coeff_79
  recurrence4A3_coeff_8
  recurrence4A3_coeff_80
  recurrence4A3_coeff_81
  recurrence4A3_coeff_82
  recurrence4A3_coeff_83
  recurrence4A3_coeff_84
  recurrence4A3_coeff_85
  recurrence4A3_coeff_86
  recurrence4A3_coeff_87
  recurrence4A3_coeff_88
  recurrence4A3_coeff_89
  recurrence4A3_coeff_9
  recurrence4A3_coeff_90
  recurrence4A3_coeff_91
  recurrence4A3_coeff_92
  recurrence4A3_coeff_93
  recurrence4A3_coeff_94
  recurrence4A3_coeff_95
  recurrence4A3_coeff_96
  recurrence4A3_coeff_97
  recurrence4A3_coeff_98
  recurrence4A3_coeff_99
  recurrence4B3_coeff_0
  recurrence4B3_coeff_1
  recurrence4B3_coeff_10
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105

attribute [local simp]
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109
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

attribute [local simp]
  recurrence4B3_coeff_164
  recurrence4B3_coeff_17
  recurrence4B3_coeff_18
  recurrence4B3_coeff_19
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

attribute [local simp]
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77
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

private theorem recurrence4B3A3_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (184 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_184 :
    recurrence4B3A3.coeff 184 =
      (((113171357813573950029975782630233896998737132963321864896592971 * 10 ^ 70 +
        5972410495284659864547159101339884584795235558985699148257501958973724) * 10 ^ 70 +
        5655015987922850811718250067782403951354097118814902569087202455715532) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (184 - x)) = _
  rw [show 185 = 2 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 23 = 3 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (185 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_185 :
    recurrence4B3A3.coeff 185 =
      -(((113060425448399150664858913237556636669612210870477656391975524 * 10 ^ 70 +
        7754915411513624202775706966982110777383089819480021462997009530541413) * 10 ^ 70 +
        8080622430977139820059212745698185773587937937123407161249983548811691) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (185 - x)) = _
  rw [show 186 = 3 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 23 = 2 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (186 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_186 :
    recurrence4B3A3.coeff 186 =
      (((106704165114835408531240882077335676792561919986853009003467663 * 10 ^ 70 +
        3164708833286604918219342486144870758836419445222230658113364053718330) * 10 ^ 70 +
        9054762632962938489054918593850882555106615184685456772197205485716388) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (186 - x)) = _
  rw [show 187 = 4 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 23 = 1 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (187 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_187 :
    recurrence4B3A3.coeff 187 =
      -(((96184965345712154891924560528894021245427013903824133248530608 * 10 ^ 70 +
        9175145628660905803320755582886972632407754180019608384617982936903078) * 10 ^ 70 +
        1635862036428235757571239533723779194471663416602226783248272836041689) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (187 - x)) = _
  rw [show 188 = 5 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4B3A3_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (188 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_188 :
    recurrence4B3A3.coeff 188 =
      (((83362218142121391397465085058050048214687956334729897151783092 * 10 ^ 70 +
        8405385533790710086465529109863579992341454926552229478545811502727275) * 10 ^ 70 +
        9434857686432379232643198312714597573523483377477697002020535680719191) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (188 - x)) = _
  rw [show 189 = 6 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 31 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (189 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_189 :
    recurrence4B3A3.coeff 189 =
      -(((69764252155390454113487667006300811408164643888885399705519543 * 10 ^ 70 +
        7286533273005139095129217462913667868675629238677408524525884464242284) * 10 ^ 70 +
        1898311328450451518536880192323182678176432417401941821313443661425722) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (189 - x)) = _
  rw [show 190 = 7 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 30 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (190 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_190 :
    recurrence4B3A3.coeff 190 =
      (((56540935632121238641848571015336562433580747698590452896949606 * 10 ^ 70 +
        1819632301460745558106075039296667651073055524725811880938175212038598) * 10 ^ 70 +
        6466919295902065022875042579064147496931631510919679155296014161035484) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (190 - x)) = _
  rw [show 191 = 8 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 29 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (191 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_191 :
    recurrence4B3A3.coeff 191 =
      -(((44467559576407088195268251142493473334797129406777160804676677 * 10 ^ 70 +
        9333562912241234723334536209885829291320171028949800821015934574473755) * 10 ^ 70 +
        7251177132119429937104201541999395587382153344023722218495422131453991) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (191 - x)) = _
  rw [show 192 = 9 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 28 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (192 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_192 :
    recurrence4B3A3.coeff 192 =
      (((33986092081925008565846876917621049165900123558429043195986225 * 10 ^ 70 +
        4799590961192246642111778503520286078759922076608844823456778061357601) * 10 ^ 70 +
        8731135101630147492606278760007807221415115398882603077227079883444114) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (192 - x)) = _
  rw [show 193 = 10 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 27 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (193 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_193 :
    recurrence4B3A3.coeff 193 =
      -(((25268602793160933642251063219001753480140246866619741344676877 * 10 ^ 70 +
        9402261576839353143764652841663657713401729851980842985849801195663185) * 10 ^ 70 +
        9008521347829888782046312765053484187873463954581297822742471889593514) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (193 - x)) = _
  rw [show 194 = 11 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 26 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (194 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_194 :
    recurrence4B3A3.coeff 194 =
      (((18288967781046788902414493066718040844951539623674398090167696 * 10 ^ 70 +
        4546834295197137134370928034124214907243681969427411736628627608653406) * 10 ^ 70 +
        9486505797335529251033758612277368150703282946685387943192898598012253) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (194 - x)) = _
  rw [show 195 = 12 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 25 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (195 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_195 :
    recurrence4B3A3.coeff 195 =
      -(((12891953855153549625074647631668512727748685306359169061897547 * 10 ^ 70 +
        5685104670147324045471014965521584040197795356784135598047619906319179) * 10 ^ 70 +
        0191062346176860198004113820653780180312234069011712735920910400731184) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (195 - x)) = _
  rw [show 196 = 13 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 24 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (196 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_196 :
    recurrence4B3A3.coeff 196 =
      (((8852480409377533299524655350663498611927748471545276161100326 * 10 ^ 70 +
        6943120275809733975712501557947777026437375591953709398319070266409687) * 10 ^ 70 +
        5795247362223650799128851326810205762581753584726604375876633876444428) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (196 - x)) = _
  rw [show 197 = 14 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 23 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (197 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_197 :
    recurrence4B3A3.coeff 197 =
      -(((5921455875539114779872850154741270858508783254019853550744011 * 10 ^ 70 +
        6390402028477755461600231985230964705955778075175882741357766618421047) * 10 ^ 70 +
        9920889258238172443333756753496399979705586460000592267786465261244599) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (197 - x)) = _
  rw [show 198 = 15 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 22 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (198 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_198 :
    recurrence4B3A3.coeff 198 =
      (((3857539466379532151650620041924524152847204589114163770918022 * 10 ^ 70 +
        4520138938511170616467135812790883446544321245065000984953321213713651) * 10 ^ 70 +
        9784390062808683493347943929676433346730869441872620520512255379736948) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (198 - x)) = _
  rw [show 199 = 16 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 21 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (199 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_199 :
    recurrence4B3A3.coeff 199 =
      -(((2446228391240631055490017012588555209745046608919956219517279 * 10 ^ 70 +
        1892512408252918813684404965923089204105412926682448015241790309127819) * 10 ^ 70 +
        7975538030529776333180523414913854724122092494525760480218707095941909) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (199 - x)) = _
  rw [show 200 = 17 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 20 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (200 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_200 :
    recurrence4B3A3.coeff 200 =
      (((1508800124841817404050897658898034517413217817627155028316172 * 10 ^ 70 +
        3383949962592361381659816615094390988434245551751534749839543531280995) * 10 ^ 70 +
        2671763119188454470097243496152939697034393595537051306240767811139654) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (200 - x)) = _
  rw [show 201 = 18 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 19 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (201 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_201 :
    recurrence4B3A3.coeff 201 =
      -(((903996703770029739680713048585932128140456348367239058874132 * 10 ^ 70 +
        7313278216770068125484681176565860192287366351740040368123968455049628) * 10 ^ 70 +
        7450551220840892806797100812026024980630069796719683658236640378956733) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (201 - x)) = _
  rw [show 202 = 19 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 18 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (202 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_202 :
    recurrence4B3A3.coeff 202 =
      (((525150741921324509368020946664079149176732231913057630249029 * 10 ^ 70 +
        9149740436661558376633160755738037129480193568144778966084619462111238) * 10 ^ 70 +
        7506589683577138639349931582270261889446792485120391890898059324578639) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (202 - x)) = _
  rw [show 203 = 20 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 17 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (203 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_203 :
    recurrence4B3A3.coeff 203 =
      -(((294956720890109109404730676545591314804267945982988723519879 * 10 ^ 70 +
        0671047023152533318122568268667613387769858272516197027859224113440988) * 10 ^ 70 +
        1899078434866223502281705322139496231640998521946709697078207211789194) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (203 - x)) = _
  rw [show 204 = 21 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 16 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (204 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_204 :
    recurrence4B3A3.coeff 204 =
      (((159483917391400096478418615366203989918328629514558912882445 * 10 ^ 70 +
        3219445844903859297253408601767546848785945249869208655820391710870958) * 10 ^ 70 +
        6214996875412214014053635403927949791900240045996754247460714825744793) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (204 - x)) = _
  rw [show 205 = 22 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 15 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (205 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_205 :
    recurrence4B3A3.coeff 205 =
      -(((82447410340927915174384568246747905766109263020094969084827 * 10 ^ 70 +
        3500184093687356386666159166899130383608804501828388185094849611051151) * 10 ^ 70 +
        7261206963073100089508812076515585865503526529265488992020447798309082) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (205 - x)) = _
  rw [show 206 = 23 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 14 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (206 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_206 :
    recurrence4B3A3.coeff 206 =
      (((40278431210591330038978782491176221296392765191375823101231 * 10 ^ 70 +
        0935625162439395971485758266310002282291243982204473305419610585947732) * 10 ^ 70 +
        5782572400867866439904700723209819706710027656291449847500826081577062) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (206 - x)) = _
  rw [show 207 = 24 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 13 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (207 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_207 :
    recurrence4B3A3.coeff 207 =
      -(((18192494151158807057540755928625671247556640030326097395172 * 10 ^ 70 +
        6786727229362711895805279323672605876030334188179118231308426557831742) * 10 ^ 70 +
        0131220477425069131925667858932198697405287785727530336759106924781994) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (207 - x)) = _
  rw [show 208 = 25 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 12 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (208 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_208 :
    recurrence4B3A3.coeff 208 =
      (((7237121988889727827123907283157273326195835080558229982532 * 10 ^ 70 +
        6286461056226720838223738474691436279566548017716781235885498976507144) * 10 ^ 70 +
        6777094799929393366393770768252171153487451328852005837512627392444331) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (208 - x)) = _
  rw [show 209 = 26 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 11 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (209 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_209 :
    recurrence4B3A3.coeff 209 =
      -(((2186403073294317144569723141105770260063448220271144075502 * 10 ^ 70 +
        3894151978612049893429395711647164113061176098872085308876190505756319) * 10 ^ 70 +
        6192451514067043900407908555737226559296843240377843875341644906799440) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (209 - x)) = _
  rw [show 210 = 27 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 10 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (210 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_210 :
    recurrence4B3A3.coeff 210 =
      (((107181253281934974758011012804139024742540675373802052941 * 10 ^ 70 +
        9999613064532315399534367668505541752752399171411698643622616534724425) * 10 ^ 70 +
        8416536067708894507427512289095794400349113018740130701931674829872680) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (210 - x)) = _
  rw [show 211 = 28 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 9 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (211 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_211 :
    recurrence4B3A3.coeff 211 =
      (((576345983622770222408220894421502738234676428911671738980 * 10 ^ 70 +
        3270547910367098539127651706594415642514683772183259627544371337848025) * 10 ^ 70 +
        5235146082585063713786259586687256211235051332136340370946653487814969) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (211 - x)) = _
  rw [show 212 = 29 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 8 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (212 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_212 :
    recurrence4B3A3.coeff 212 =
      -(((668212724200391626704139195026111524371485038639654328674 * 10 ^ 70 +
        0857112843976209795468326771587503374667793567044057479148312626288568) * 10 ^ 70 +
        4018235844929937115708469450876846482119976724796935306138391976399990) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (212 - x)) = _
  rw [show 213 = 30 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 7 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (213 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_213 :
    recurrence4B3A3.coeff 213 =
      (((552581326976597178010152827646448533026036717150633541010 * 10 ^ 70 +
        4686918170684869905782767754083194719256178244971599047458018955673845) * 10 ^ 70 +
        9022616849221678957156647127252050742828990876872203675911117027160901) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (213 - x)) = _
  rw [show 214 = 31 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 6 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (214 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_214 :
    recurrence4B3A3.coeff 214 =
      -(((396514273561228305149263889446241818881727151869099717091 * 10 ^ 70 +
        0963378481865147420251067178425322056074214793370053673628799521621852) * 10 ^ 70 +
        3502586174085354056486443600476881533679284384646802082949019280603456) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (214 - x)) = _
  rw [show 215 = 32 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 5 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (215 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_215 :
    recurrence4B3A3.coeff 215 =
      (((261688463192346639277298366685416834299094369877645314046 * 10 ^ 70 +
        1780751041369909840544549745545474104504856627191243527900077271114752) * 10 ^ 70 +
        1127677630388275401403717776953134169044057440621934199083012326177612) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (215 - x)) = _
  rw [show 216 = 33 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 4 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
