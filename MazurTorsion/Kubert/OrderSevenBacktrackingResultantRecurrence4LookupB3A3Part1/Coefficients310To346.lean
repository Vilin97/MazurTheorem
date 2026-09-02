/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3Part1Simp
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
  recurrence4A3_coeff_150
  recurrence4A3_coeff_151
  recurrence4A3_coeff_152
  recurrence4A3_coeff_153
  recurrence4A3_coeff_154
  recurrence4A3_coeff_155
  recurrence4A3_coeff_156
  recurrence4A3_coeff_157
  recurrence4A3_coeff_158
  recurrence4A3_coeff_159
  recurrence4A3_coeff_160
  recurrence4A3_coeff_161
  recurrence4A3_coeff_162
  recurrence4A3_coeff_163

attribute [local simp]
  recurrence4A3_coeff_164
  recurrence4A3_coeff_165
  recurrence4A3_coeff_166
  recurrence4A3_coeff_167
  recurrence4A3_coeff_168
  recurrence4A3_coeff_169
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
  recurrence4A3_coeff_180
  recurrence4A3_coeff_181
  recurrence4A3_coeff_182
  recurrence4A3_coeff_52
  recurrence4A3_coeff_53
  recurrence4A3_coeff_54
  recurrence4A3_coeff_55
  recurrence4A3_coeff_56
  recurrence4A3_coeff_57
  recurrence4A3_coeff_58
  recurrence4A3_coeff_59
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
  recurrence4A3_coeff_90
  recurrence4A3_coeff_91
  recurrence4A3_coeff_92
  recurrence4A3_coeff_93
  recurrence4A3_coeff_94
  recurrence4A3_coeff_95
  recurrence4A3_coeff_96

attribute [local simp]
  recurrence4A3_coeff_97
  recurrence4A3_coeff_98
  recurrence4A3_coeff_99
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
  recurrence4B3_coeff_160

attribute [local simp]
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163
  recurrence4B3_coeff_164
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
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
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
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
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93

attribute [local simp]
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

private theorem recurrence4B3A3_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (310 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_310 :
    recurrence4B3A3.coeff 310 =
      -(((8166480 * 10 ^ 70 +
        4516128630941084092026038293921867358597725756502809968831736967717075) * 10 ^ 70 +
        4731005718893817726240438652887687669656223872090880244989485340837155) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (310 - x)) = _
  rw [show 311 = 128 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 5 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (311 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_311 :
    recurrence4B3A3.coeff 311 =
      (((2240525 * 10 ^ 70 +
        7319983109516943300211275286599326035583257707231574689025573686082111) * 10 ^ 70 +
        5531075211959961993981934276861003389641100779360679615485994031671588) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (311 - x)) = _
  rw [show 312 = 129 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 4 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (312 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_312 :
    recurrence4B3A3.coeff 312 =
      -(((204917 * 10 ^ 70 +
        1575050785750216940847369985174997454992682047584624786846303443483607) * 10 ^ 70 +
        9377978343683187331852870929566717617122621471207609307990657011496828) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (312 - x)) = _
  rw [show 313 = 130 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 3 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (313 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_313 :
    recurrence4B3A3.coeff 313 =
      (((10483 * 10 ^ 70 +
        7820410902268148236355586711144779101218616435556789334143137897892501) * 10 ^ 70 +
        6822287957715437834107381556663713053298314183593036543625623942641397) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (313 - x)) = _
  rw [show 314 = 131 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 2 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (314 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_314 :
    recurrence4B3A3.coeff 314 =
      -(((181 * 10 ^ 70 +
        2605010098219197355862098587864923965283923247190377093799334246328145) * 10 ^ 70 +
        7119609377758410930907137667225818025278603897737437886426133059241660) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (314 - x)) = _
  rw [show 315 = 132 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 1 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (315 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_315 :
    recurrence4B3A3.coeff 315 =
      -(((15 * 10 ^ 70 +
        5868348938052610382906352076753718391412462847420577304753287069869472) * 10 ^ 70 +
        1061901066252889297710900147119053176262338268438388678094558412155443) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (315 - x)) = _
  rw [show 316 = 133 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (316 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_316 :
    recurrence4B3A3.coeff 316 =
      (((1 * 10 ^ 70 +
        2779243995993513209732663323458124153942772012078435867293862970963691) * 10 ^ 70 +
        1560115160698592202667808273033700188817974808969859729551656043732753) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (316 - x)) = _
  rw [show 317 = 134 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 31 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (317 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_317 :
    recurrence4B3A3.coeff 317 =
      -((317330627654217927513646629430620937703208792437694326518896027399846 * 10 ^ 70 +
        9868700659074632124382432469520586231209879900295293101573498500118295) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (317 - x)) = _
  rw [show 318 = 135 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 30 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (318 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_318 :
    recurrence4B3A3.coeff 318 =
      -((5574553762225364730270374481381245788282690118943645090392666321990 * 10 ^ 70 +
        7794682829727789728385253064951361319405222288094216713262714990363745) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (318 - x)) = _
  rw [show 319 = 136 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 29 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (319 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_319 :
    recurrence4B3A3.coeff 319 =
      ((427882495424271404063921190374980547599717348877874646432677364713 * 10 ^ 70 +
        3119813578208334202928951345175719111125560673885800834092899411753063) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (319 - x)) = _
  rw [show 320 = 137 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 28 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (320 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_320 :
    recurrence4B3A3.coeff 320 =
      -((1575810441584659592235991083819609706001859068070067095944294764 * 10 ^ 70 +
        2953865673918564850217387618083219159923562502361350165782077902846610) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (320 - x)) = _
  rw [show 321 = 138 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 27 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (321 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_321 :
    recurrence4B3A3.coeff 321 =
      -((200106119016883849057575081102329832389066520130639342489022975 * 10 ^ 70 +
        7864490674812043303084662457604831334339873255969893206445481492537674) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (321 - x)) = _
  rw [show 322 = 139 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 26 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (322 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_322 :
    recurrence4B3A3.coeff 322 =
      -((293060071971965252058838075360775851430710243919083327073279 * 10 ^ 70 +
        6466946528580022743568151013463476807329541090362690515206142629563358) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (322 - x)) = _
  rw [show 323 = 140 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 25 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (323 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_323 :
    recurrence4B3A3.coeff 323 =
      ((31473773542116605867524346515895291259965244236146774152210 * 10 ^ 70 +
        7874119695026904505095476950133747934522273952136799899035332231691661) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (323 - x)) = _
  rw [show 324 = 141 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 24 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (324 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_324 :
    recurrence4B3A3.coeff 324 =
      ((238537492799216512239845012553089252287045226110124150211 * 10 ^ 70 +
        5620871676227918393337011569108152922340903929037746156523409630203829) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (324 - x)) = _
  rw [show 325 = 142 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 23 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (325 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_325 :
    recurrence4B3A3.coeff 325 =
      -((251473147568101933861687218486926663765461805101743617 * 10 ^ 70 +
        5026804860613764078902133680383832400630310154240861041237973554919330) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (325 - x)) = _
  rw [show 326 = 143 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 22 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (326 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_326 :
    recurrence4B3A3.coeff 326 =
      -((7943795490208979660731966067078416402396322330642522 * 10 ^ 70 +
        7784406139579207214086300612147736024950539908803681327363331435677257) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (326 - x)) = _
  rw [show 327 = 144 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 21 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (327 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_327 :
    recurrence4B3A3.coeff 327 =
      -((19572123682627594333355280293530555853560363889726 * 10 ^ 70 +
        4888996514519526668529162249216550890541986681254422960000180313659206) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (327 - x)) = _
  rw [show 328 = 145 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 20 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (328 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_328 :
    recurrence4B3A3.coeff 328 =
      ((49044383273069594192215275324609207071273977446 * 10 ^ 70 +
        6921118333425870886547895626665093204877151782959119700063431593177349) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (328 - x)) = _
  rw [show 329 = 146 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 19 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (329 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_329 :
    recurrence4B3A3.coeff 329 =
      ((218709142101810839237031500354437963693586138 * 10 ^ 70 +
        4579222343651986271261463427304159119087993809946306673236354068529789) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (329 - x)) = _
  rw [show 330 = 147 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 18 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (330 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_330 :
    recurrence4B3A3.coeff 330 =
      -((60004249742314093267578794505736980946052 * 10 ^ 70 +
        1105745174715541101482667058952703227816928851904477850765610849585478) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (330 - x)) = _
  rw [show 331 = 148 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 17 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (331 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_331 :
    recurrence4B3A3.coeff 331 =
      -((840638672159945688743309984756051385286 * 10 ^ 70 +
        8388367790896634248341095998622976500818219655659074550094455143574590) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (331 - x)) = _
  rw [show 332 = 149 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 16 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (332 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_332 :
    recurrence4B3A3.coeff 332 =
      -((165659312141218293867449781303076216 * 10 ^ 70 +
        2046031640619215027073065749503410593348133922449287338762814837606655) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (332 - x)) = _
  rw [show 333 = 150 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 15 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (333 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_333 :
    recurrence4B3A3.coeff 333 =
      ((1212001109888034307098170814910321 * 10 ^ 70 +
        7912392627639626502438776679015621806331289963656344347858379244799983) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (333 - x)) = _
  rw [show 334 = 151 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 14 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (334 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_334 :
    recurrence4B3A3.coeff 334 =
      ((328860541003318769874109782885 * 10 ^ 70 +
        8053413055461951673209807210728983565833526526049463871258386162152279) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (334 - x)) = _
  rw [show 335 = 152 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 13 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (335 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_335 :
    recurrence4B3A3.coeff 335 =
      -((369500153938215449772847787 * 10 ^ 70 +
        9351561765160702305709875762529361571665332434167421323643597521176251) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (335 - x)) = _
  rw [show 336 = 153 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 12 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (336 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_336 :
    recurrence4B3A3.coeff 336 =
      -((66536024543333453476876 * 10 ^ 70 +
        5450429728863595495519312035827577652856927836333371756100495037165913) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (336 - x)) = _
  rw [show 337 = 154 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 11 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (337 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_337 :
    recurrence4B3A3.coeff 337 =
      ((12158166416674343972 * 10 ^ 70 +
        9002068886828204118173479283073346698071546516559989376961435496564061) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (337 - x)) = _
  rw [show 338 = 155 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 10 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (338 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_338 :
    recurrence4B3A3.coeff 338 =
      ((982969062409953 * 10 ^ 70 +
        7034253323484021467754744900538373403774585602812795169936281113722707) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (338 - x)) = _
  rw [show 339 = 156 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 9 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (339 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_339 :
    recurrence4B3A3.coeff 339 =
      -((28695655203 * 10 ^ 70 +
        2055258521498779536182837052564263457142942940090194521729540794731061) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (339 - x)) = _
  rw [show 340 = 157 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 8 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (340 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_340 :
    recurrence4B3A3.coeff 340 =
      -((754026 * 10 ^ 70 +
        8708015096502294711013361743276974093548983857075751147043306978783578) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (340 - x)) = _
  rw [show 341 = 158 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 7 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (341 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_341 :
    recurrence4B3A3.coeff 341 =
      ((2 * 10 ^ 70 +
        9956417577900696938560386782097165574218696177621852968589296437430283) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (341 - x)) = _
  rw [show 342 = 159 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 6 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (342 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_342 :
    recurrence4B3A3.coeff 342 =
      (166200577260865696213783152421897361960008116830691993548602083809 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (342 - x)) = _
  rw [show 343 = 160 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 5 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (343 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_343 :
    recurrence4B3A3.coeff 343 =
      (-65964408095844150986211479570731191572132853184750281546146 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (343 - x)) = _
  rw [show 344 = 161 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 4 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (344 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_344 :
    recurrence4B3A3.coeff 344 =
      (-37067519174062366567404384624756845455296850857098735 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (344 - x)) = _
  rw [show 345 = 162 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 3 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (345 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_345 :
    recurrence4B3A3.coeff 345 =
      (784397845382310995461708061609246340245151660 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (345 - x)) = _
  rw [show 346 = 163 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 2 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (346 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_346 :
    recurrence4B3A3.coeff 346 =
      (8446737236647738989518319492449559300 : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (346 - x)) = _
  rw [show 347 = 164 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 1 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
