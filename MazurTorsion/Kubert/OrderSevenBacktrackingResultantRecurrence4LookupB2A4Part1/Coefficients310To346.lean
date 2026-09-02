/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2A4Part1Simp
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
  recurrence4A4_coeff_150
  recurrence4A4_coeff_151
  recurrence4A4_coeff_152
  recurrence4A4_coeff_153
  recurrence4A4_coeff_154
  recurrence4A4_coeff_155
  recurrence4A4_coeff_156
  recurrence4A4_coeff_157
  recurrence4A4_coeff_158
  recurrence4A4_coeff_159
  recurrence4A4_coeff_160
  recurrence4A4_coeff_161
  recurrence4A4_coeff_162
  recurrence4A4_coeff_163

attribute [local simp]
  recurrence4A4_coeff_164
  recurrence4A4_coeff_165
  recurrence4A4_coeff_166
  recurrence4A4_coeff_167
  recurrence4A4_coeff_168
  recurrence4A4_coeff_169
  recurrence4A4_coeff_170
  recurrence4A4_coeff_171
  recurrence4A4_coeff_172
  recurrence4A4_coeff_173
  recurrence4A4_coeff_174
  recurrence4A4_coeff_175
  recurrence4A4_coeff_176
  recurrence4A4_coeff_177
  recurrence4A4_coeff_178
  recurrence4A4_coeff_48
  recurrence4A4_coeff_49
  recurrence4A4_coeff_50
  recurrence4A4_coeff_51
  recurrence4A4_coeff_52
  recurrence4A4_coeff_53
  recurrence4A4_coeff_54
  recurrence4A4_coeff_55
  recurrence4A4_coeff_56
  recurrence4A4_coeff_57
  recurrence4A4_coeff_58
  recurrence4A4_coeff_59
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
  recurrence4A4_coeff_90
  recurrence4A4_coeff_91
  recurrence4A4_coeff_92
  recurrence4A4_coeff_93
  recurrence4A4_coeff_94
  recurrence4A4_coeff_95
  recurrence4A4_coeff_96

attribute [local simp]
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99
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
  recurrence4B2_coeff_160

attribute [local simp]
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167
  recurrence4B2_coeff_168
  recurrence4B2_coeff_38
  recurrence4B2_coeff_39
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
  recurrence4B2_coeff_70
  recurrence4B2_coeff_71
  recurrence4B2_coeff_72
  recurrence4B2_coeff_73
  recurrence4B2_coeff_74
  recurrence4B2_coeff_75
  recurrence4B2_coeff_76
  recurrence4B2_coeff_77
  recurrence4B2_coeff_78
  recurrence4B2_coeff_79
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
  recurrence4B2_coeff_90
  recurrence4B2_coeff_91
  recurrence4B2_coeff_92
  recurrence4B2_coeff_93

attribute [local simp]
  recurrence4B2_coeff_94
  recurrence4B2_coeff_95
  recurrence4B2_coeff_96
  recurrence4B2_coeff_97
  recurrence4B2_coeff_98
  recurrence4B2_coeff_99

private theorem recurrence4B2A4_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (310 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_310 :
    recurrence4B2A4.coeff 310 =
      -(((2426879 * 10 ^ 70 +
        7005241794406031254001876774281616385355382098172599886296188015900363) * 10 ^ 70 +
        7646088731700536798726260509619813173455968331016854581297898312641864) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (310 - x)) = _
  rw [show 311 = 132 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 5 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (311 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_311 :
    recurrence4B2A4.coeff 311 =
      (((953617 * 10 ^ 70 +
        8645877872853929176137989013666584011019410402809075598280603733948241) * 10 ^ 70 +
        1879080357353008548068499562444643369207029449219059514058519222562420) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (311 - x)) = _
  rw [show 312 = 133 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 4 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (312 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_312 :
    recurrence4B2A4.coeff 312 =
      -(((93203 * 10 ^ 70 +
        2849279524029239157603389191220187307931978251671373989005803263603382) * 10 ^ 70 +
        6422055436972905115337216294101584275959337619638337487362983821461378) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (312 - x)) = _
  rw [show 313 = 134 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 3 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (313 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_313 :
    recurrence4B2A4.coeff 313 =
      (((4843 * 10 ^ 70 +
        3156732422056183609708259696817933235547458208570340891689383783366612) * 10 ^ 70 +
        1330429343799815802372252422679826897527783810160774209003299553716813) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (313 - x)) = _
  rw [show 314 = 135 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 2 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (314 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_314 :
    recurrence4B2A4.coeff 314 =
      -(((68 * 10 ^ 70 +
        4140051148764314415622918823790690603989639265264417063863540557702250) * 10 ^ 70 +
        2078801828714260169753575420338647767947142327082457487619822451476529) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (314 - x)) = _
  rw [show 315 = 136 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 1 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (315 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_315 :
    recurrence4B2A4.coeff 315 =
      -(((9 * 10 ^ 70 +
        2919673529546381730504313083152311422790624548799257258428519977148671) * 10 ^ 70 +
        5415845829084746931045846917932197046391735237734454936997338088588322) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (315 - x)) = _
  rw [show 316 = 137 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (316 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_316 :
    recurrence4B2A4.coeff 316 =
      ((6981075558843972923959043129157107281919279637579487702009532194894696 * 10 ^ 70 +
        2533221282039255847449706494749761800056403394164716970273343957060138) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (316 - x)) = _
  rw [show 317 = 138 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 31 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (317 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_317 :
    recurrence4B2A4.coeff 317 =
      -((153260271017824119043491764829248609887315415097629977248135424067217 * 10 ^ 70 +
        0678000704885915716709846660457514496594338328278073901264226550170757) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (317 - x)) = _
  rw [show 318 = 139 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 30 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (318 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_318 :
    recurrence4B2A4.coeff 318 =
      -((4312819256342646595360912549053798113015763832502801997501190209102 * 10 ^ 70 +
        8897130006449086456967164584948130009691192753214252851971590646181685) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (318 - x)) = _
  rw [show 319 = 140 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 29 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (319 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_319 :
    recurrence4B2A4.coeff 319 =
      ((254628762576869696739118369269542170846058949328207630191638150747 * 10 ^ 70 +
        7935939686383188159408617938650859429563848880606997840484357059333151) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (319 - x)) = _
  rw [show 320 = 141 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 28 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (320 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_320 :
    recurrence4B2A4.coeff 320 =
      -((35651516526360356051641037949440855580479276500190432099966880 * 10 ^ 70 +
        1070185375300751501271111839665228224321521443011378502226414183644586) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (320 - x)) = _
  rw [show 321 = 142 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 27 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (321 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_321 :
    recurrence4B2A4.coeff 321 =
      -((130737908207730229776037945259429197231096328189770819789366746 * 10 ^ 70 +
        9989082132834056188685270539237535300037143557945997454737822844589944) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (321 - x)) = _
  rw [show 322 = 143 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 26 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (322 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_322 :
    recurrence4B2A4.coeff 322 =
      -((564440026347254940793009196366959802519537011901391133572922 * 10 ^ 70 +
        0499280432588684211684679188604222845612169213805900448980755355620947) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (322 - x)) = _
  rw [show 323 = 144 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 25 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (323 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_323 :
    recurrence4B2A4.coeff 323 =
      ((18788302206621630086648019558506813858382315252774485058652 * 10 ^ 70 +
        7047650544165872695510848921211853781694422666819840797006182029334569) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (323 - x)) = _
  rw [show 324 = 145 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 24 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (324 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_324 :
    recurrence4B2A4.coeff 324 =
      ((187090783483944631357069287773962056234610439607932355652 * 10 ^ 70 +
        2852085137750738813926655554596135642513001606373590079662527643836907) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (324 - x)) = _
  rw [show 325 = 146 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 23 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (325 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_325 :
    recurrence4B2A4.coeff 325 =
      ((124373934960997919063109968673268645696976391060340545 * 10 ^ 70 +
        6118313469148574056292300211738784235458376610878514481069838471432465) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (325 - x)) = _
  rw [show 326 = 147 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 22 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (326 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_326 :
    recurrence4B2A4.coeff 326 =
      -((4948528611825188672386914355707747553592431860564250 * 10 ^ 70 +
        3499859765255646494014511700034599210999449909260596071061432154586320) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (326 - x)) = _
  rw [show 327 = 148 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 21 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (327 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_327 :
    recurrence4B2A4.coeff 327 =
      -((17679679668544563604902579989534977432456270748474 * 10 ^ 70 +
        3959799275897437590376029383667182896489173541390800311273989892847034) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (327 - x)) = _
  rw [show 328 = 149 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 20 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (328 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_328 :
    recurrence4B2A4.coeff 328 =
      ((18533514375464068808609940178496099773360282478 * 10 ^ 70 +
        3153947049721735009560672353723236495123244828837827356219083977186960) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (328 - x)) = _
  rw [show 329 = 150 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 19 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (329 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_329 :
    recurrence4B2A4.coeff 329 =
      ((164709408490153736642074785526524898779350322 * 10 ^ 70 +
        4951613071870204153034809560842782040788115498347130660719797456315211) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (329 - x)) = _
  rw [show 330 = 151 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 18 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (330 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_330 :
    recurrence4B2A4.coeff 330 =
      ((61057170048032934196926569993608743373440 * 10 ^ 70 +
        1437626296383670928426018839504505620147841765784784443749177235351617) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (330 - x)) = _
  rw [show 331 = 152 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 17 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (331 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_331 :
    recurrence4B2A4.coeff 331 =
      -((572242622251129708041069151467829450155 * 10 ^ 70 +
        9756592586475286540963918760559596217884361544344479799388212414539761) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (331 - x)) = _
  rw [show 332 = 153 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 16 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (332 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_332 :
    recurrence4B2A4.coeff 332 =
      -((377261593122582386554150624852513019 * 10 ^ 70 +
        4898762851610150835869404058381015016498520644578598294835072188272599) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (332 - x)) = _
  rw [show 333 = 154 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 15 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (333 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_333 :
    recurrence4B2A4.coeff 333 =
      ((774017192556181594649884759250814 * 10 ^ 70 +
        3536723498260231809130676252872744998696364719860609029849643820502627) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (333 - x)) = _
  rw [show 334 = 155 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 14 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (334 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_334 :
    recurrence4B2A4.coeff 334 =
      ((445254129689738669024291137074 * 10 ^ 70 +
        4942055974573176741980757157998381958591022013603036725986252448234055) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (334 - x)) = _
  rw [show 335 = 156 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 13 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (335 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_335 :
    recurrence4B2A4.coeff 335 =
      -((211020017000042375387498476 * 10 ^ 70 +
        2718615325381931145053786548474051974892720556639475950110273719714352) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (335 - x)) = _
  rw [show 336 = 157 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (336 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_336 :
    recurrence4B2A4.coeff 336 =
      -((73307669320134453506466 * 10 ^ 70 +
        1238985107099445961648116298173093140312277404241953514443288013287510) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (336 - x)) = _
  rw [show 337 = 158 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 11 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (337 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_337 :
    recurrence4B2A4.coeff 337 =
      ((5594648076139424798 * 10 ^ 70 +
        7958652502912171488851280403286461943252743796258086056742597433596462) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (337 - x)) = _
  rw [show 338 = 159 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 10 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (338 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_338 :
    recurrence4B2A4.coeff 338 =
      ((988142602102956 * 10 ^ 70 +
        6441175207260761708862216806934574274019941627550929742044557509510339) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (338 - x)) = _
  rw [show 339 = 160 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 9 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (339 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_339 :
    recurrence4B2A4.coeff 339 =
      -((8701298836 * 10 ^ 70 +
        9830241641612214648367887198325367518288287661905002485961690601331236) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (339 - x)) = _
  rw [show 340 = 161 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 8 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (340 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_340 :
    recurrence4B2A4.coeff 340 =
      -((728020 * 10 ^ 70 +
        8867836846495308044276361987838315667169963267641876312853503563239516) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (340 - x)) = _
  rw [show 341 = 162 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 7 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (341 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_341 :
    recurrence4B2A4.coeff 341 =
      (3185543875939114963364936652804658032464191347705789672736416071466453 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (341 - x)) = _
  rw [show 342 = 163 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 6 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (342 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_342 :
    recurrence4B2A4.coeff 342 =
      (159440874692401052299120222210323802881303753869109880618637329801 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (342 - x)) = _
  rw [show 343 = 164 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 5 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (343 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_343 :
    recurrence4B2A4.coeff 343 =
      (3892928270344226532973363258922245384633289925025687392201 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (343 - x)) = _
  rw [show 344 = 165 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 4 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (344 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_344 :
    recurrence4B2A4.coeff 344 =
      (-36545089356850225515065744663586451481290633989024751 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (344 - x)) = _
  rw [show 345 = 166 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 3 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (345 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_345 :
    recurrence4B2A4.coeff 345 =
      (49421852271526131723191755307298837574818749 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (345 - x)) = _
  rw [show 346 = 167 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 2 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (346 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_346 :
    recurrence4B2A4.coeff 346 =
      (8644687378941815133797349621600670141 : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (346 - x)) = _
  rw [show 347 = 168 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 1 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
