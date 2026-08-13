/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4Part1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3A4 coefficient convolution

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
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99

attribute [local simp]
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
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163

attribute [local simp]
  recurrence4B3_coeff_164
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
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

private theorem recurrence4B3A4_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (307 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_307 :
    recurrence4B3A4.coeff 307 =
      (((2426150 * 10 ^ 70 +
        6302112143286515028942816882357035215921028103043677995314360221264289) * 10 ^ 70 +
        4403362117991416744051079447002960450902893725893499772632914231074887) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (307 - x)) = _
  rw [show 308 = 129 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 4 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (308 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_308 :
    recurrence4B3A4.coeff 308 =
      -(((161409 * 10 ^ 70 +
        8666487565620689879171321454274732084034074835266381079252136032380649) * 10 ^ 70 +
        4564792210850415379122028729963216568416126001159972443684324762616856) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (308 - x)) = _
  rw [show 309 = 130 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 3 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (309 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_309 :
    recurrence4B3A4.coeff 309 =
      (((5805 * 10 ^ 70 +
        9890530821062925985161891203397126946492056162150549582492245655971898) * 10 ^ 70 +
        7200619788445216502007167131823593314053877979516157877351092446639808) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (309 - x)) = _
  rw [show 310 = 131 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 2 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (310 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_310 :
    recurrence4B3A4.coeff 310 =
      (((49 * 10 ^ 70 +
        6973347303390780696737018907444647324074857031671227363739939148022225) * 10 ^ 70 +
        5437141191897960068900028626671746039277281446479730371499316659006157) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (310 - x)) = _
  rw [show 311 = 132 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 1 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (311 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_311 :
    recurrence4B3A4.coeff 311 =
      -(((19 * 10 ^ 70 +
        0881074132447707955981692828734785654434466147240669288697312333122562) * 10 ^ 70 +
        8067076638587157565882662795815097271599741887814045511668872320517353) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (311 - x)) = _
  rw [show 312 = 133 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (312 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_312 :
    recurrence4B3A4.coeff 312 =
      (((1 * 10 ^ 70 +
        0100082882441755146073581235670500227462990175396389360075222900911401) * 10 ^ 70 +
        8907061893286144718448214223432177738708339004266821077007422467111141) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (312 - x)) = _
  rw [show 313 = 134 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 31 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (313 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_313 :
    recurrence4B3A4.coeff 313 =
      -((151180559054390631935768272158739620829297957561744860174430844020064 * 10 ^ 70 +
        0694487704844839130235695270160464652678412335688242537158463776706674) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (313 - x)) = _
  rw [show 314 = 135 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 30 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (314 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_314 :
    recurrence4B3A4.coeff 314 =
      -((7629277740819337564623533282902789238343906276038338762000163755286 * 10 ^ 70 +
        5453845105643900191776991276675536713531895755344796334986467761267122) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (314 - x)) = _
  rw [show 315 = 136 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 29 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (315 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_315 :
    recurrence4B3A4.coeff 315 =
      ((329738798763536250116249985873351911115034226430064093281965802098 * 10 ^ 70 +
        9687018519657757032110114857589159710626658050181156762553306072974975) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (315 - x)) = _
  rw [show 316 = 137 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 28 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (316 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_316 :
    recurrence4B3A4.coeff 316 =
      ((706627098538555179323563847416251733192052216569140121193241091 * 10 ^ 70 +
        5246839822640564717642988521740600983355052355183501666580839185841863) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (316 - x)) = _
  rw [show 317 = 138 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 27 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (317 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_317 :
    recurrence4B3A4.coeff 317 =
      -((166411573156517844664884976114985206234480818880420283008594635 * 10 ^ 70 +
        3688044856837901086397231251217552506585855865094007782962420857269292) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (317 - x)) = _
  rw [show 318 = 139 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 26 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (318 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_318 :
    recurrence4B3A4.coeff 318 =
      -((697234139504619110568223943311327535980760783486300703666081 * 10 ^ 70 +
        8743338623122932711902926926851482215410429868594286539402752593890429) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (318 - x)) = _
  rw [show 319 = 140 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 25 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (319 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_319 :
    recurrence4B3A4.coeff 319 =
      ((25348154732708195135096719468081189457721950349007423912743 * 10 ^ 70 +
        2220947253791680026456346793800503744595546391475109792504925051770870) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (319 - x)) = _
  rw [show 320 = 141 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 24 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (320 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_320 :
    recurrence4B3A4.coeff 320 =
      ((239205521392227763092018275537064152769979578384911544989 * 10 ^ 70 +
        1198213118851018124909578862508830729741876925736607909805979452884634) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (320 - x)) = _
  rw [show 321 = 142 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 23 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (321 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_321 :
    recurrence4B3A4.coeff 321 =
      -((2324099666444241757148387128176363760905753234367882 * 10 ^ 70 +
        2102940585628268676622366011059510069511751526792742163237353781937826) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (321 - x)) = _
  rw [show 322 = 143 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 22 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (322 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_322 :
    recurrence4B3A4.coeff 322 =
      -((7377186380597392882336396305965986785207103985965293 * 10 ^ 70 +
        2168297745347805090010917857591144024684560300882285795940915723909780) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (322 - x)) = _
  rw [show 323 = 144 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 21 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (323 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_323 :
    recurrence4B3A4.coeff 323 =
      -((23157349412720647199961812249699212666555361226805 * 10 ^ 70 +
        7582707831071136158879688216642700111195294053886606796125772338949148) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (323 - x)) = _
  rw [show 324 = 145 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 20 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (324 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_324 :
    recurrence4B3A4.coeff 324 =
      ((37215880863582041008400949859368698140755343983 * 10 ^ 70 +
        5081198725246236253843920819360166543438367259256059854516856372395516) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (324 - x)) = _
  rw [show 325 = 146 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 19 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (325 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_325 :
    recurrence4B3A4.coeff 325 =
      ((240457175124432748223982525243957413606356836 * 10 ^ 70 +
        2085706051900174120621716121735160927691861644725847409965817492074968) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (325 - x)) = _
  rw [show 326 = 147 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 18 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (326 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_326 :
    recurrence4B3A4.coeff 326 =
      ((26233067116942477577060757573858847124160 * 10 ^ 70 +
        8371478537121960162561097271400731091578713136279133608852314322851779) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (326 - x)) = _
  rw [show 327 = 148 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 17 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (327 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_327 :
    recurrence4B3A4.coeff 327 =
      -((910425048878492487207338451629469407381 * 10 ^ 70 +
        9278994800481357450288242596257661759336509942568622253604514362609863) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (327 - x)) = _
  rw [show 328 = 149 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 16 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (328 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_328 :
    recurrence4B3A4.coeff 328 =
      -((428355539847926311572658624395038248 * 10 ^ 70 +
        0361083897205547582034902650387982302479720663516850258198644457878043) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (328 - x)) = _
  rw [show 329 = 150 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 15 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (329 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_329 :
    recurrence4B3A4.coeff 329 =
      ((1342527882549121917151999130204344 * 10 ^ 70 +
        5878083444395964082269965986408980615886633678590049724652198955484427) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (329 - x)) = _
  rw [show 330 = 151 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 14 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (330 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_330 :
    recurrence4B3A4.coeff 330 =
      ((600607385899269656305003742482 * 10 ^ 70 +
        3373205723775023733237817417675921298755014442203298006804841135273279) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (330 - x)) = _
  rw [show 331 = 152 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 13 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (331 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_331 :
    recurrence4B3A4.coeff 331 =
      -((433046799005802435781488911 * 10 ^ 70 +
        9004577671544857594964810268490189745337640304069759533087791243955209) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (331 - x)) = _
  rw [show 332 = 153 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (332 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_332 :
    recurrence4B3A4.coeff 332 =
      -((118688360847302617950182 * 10 ^ 70 +
        2377836523527105353798187862201597897932247198952480195533069026983398) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (332 - x)) = _
  rw [show 333 = 154 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 11 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (333 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_333 :
    recurrence4B3A4.coeff 333 =
      ((15083837867884666381 * 10 ^ 70 +
        8355544097756873469628750295126057073679552296990065450414149968432239) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (333 - x)) = _
  rw [show 334 = 155 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 10 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (334 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_334 :
    recurrence4B3A4.coeff 334 =
      ((1937018098315750 * 10 ^ 70 +
        6912004504424788689234805386985231853146692642409340501069117308364897) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (334 - x)) = _
  rw [show 335 = 156 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 9 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (335 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_335 :
    recurrence4B3A4.coeff 335 =
      -((37234255610 * 10 ^ 70 +
        7214639938930088712137988031203787055631346063421151059647160868476309) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (335 - x)) = _
  rw [show 336 = 157 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 8 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (336 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_336 :
    recurrence4B3A4.coeff 336 =
      -((1769622 * 10 ^ 70 +
        0443168808919257720113164189418356213691776949453438172088986284742262) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (336 - x)) = _
  rw [show 337 = 158 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 7 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (337 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_337 :
    recurrence4B3A4.coeff 337 =
      ((4 * 10 ^ 70 +
        0340688137721530789091017979358661860009364964993702298318398011262667) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (337 - x)) = _
  rw [show 338 = 159 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 6 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (338 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_338 :
    recurrence4B3A4.coeff 338 =
      (504017678327847682915086885677927800554808002053473611490763774507 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (338 - x)) = _
  rw [show 339 = 160 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 5 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (339 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_339 :
    recurrence4B3A4.coeff 339 =
      (-100762257592350468113657032443957682948882773522607516144985 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (339 - x)) = _
  rw [show 340 = 161 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 4 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (340 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_340 :
    recurrence4B3A4.coeff 340 =
      (-164307136086778267567799254222819600906248373976475560 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (340 - x)) = _
  rw [show 341 = 162 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 3 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (341 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_341 :
    recurrence4B3A4.coeff 341 =
      (2235913438855190091535226669145218491828049229 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (341 - x)) = _
  rw [show 342 = 163 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 2 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (342 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_342 :
    recurrence4B3A4.coeff 342 =
      (68130461165797460872098471860624747870 : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (342 - x)) = _
  rw [show 343 = 164 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 1 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
