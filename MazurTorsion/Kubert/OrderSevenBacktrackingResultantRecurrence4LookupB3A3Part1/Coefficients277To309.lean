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

private theorem recurrence4B3A3_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (277 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_277 :
    recurrence4B3A3.coeff 277 =
      -(((3063651656732604211931989007504 * 10 ^ 70 +
        8821460794853623261748518383760504603639349093530628470920505606808284) * 10 ^ 70 +
        8436074289495589486318098692498506688810772608650235061229075114649265) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (277 - x)) = _
  rw [show 278 = 95 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 6 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (278 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_278 :
    recurrence4B3A3.coeff 278 =
      (((1709176358855942704205178355329 * 10 ^ 70 +
        9228204533384163457438416703750733016285572122389797574863418398685927) * 10 ^ 70 +
        1300246899587191090477217816277164482093420137997879455051817548426010) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (278 - x)) = _
  rw [show 279 = 96 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 5 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (279 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_279 :
    recurrence4B3A3.coeff 279 =
      -(((801147130009384020618825547386 * 10 ^ 70 +
        3384774184793584637731471728151228670129775938948204110430095284262357) * 10 ^ 70 +
        1250899189525791480968042486754863592372502836456232193911782024611796) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (279 - x)) = _
  rw [show 280 = 97 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 4 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (280 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_280 :
    recurrence4B3A3.coeff 280 =
      (((339179497499419693617083899494 * 10 ^ 70 +
        6425093802959113444218645521649656109621986585807042680211337433004152) * 10 ^ 70 +
        6215236772323427575931174630477379364882483837851500186219313823304389) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (280 - x)) = _
  rw [show 281 = 98 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 3 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (281 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_281 :
    recurrence4B3A3.coeff 281 =
      -(((133190659108577635940029708535 * 10 ^ 70 +
        6835320184426083940406224530836709265143116703511565673039553877469120) * 10 ^ 70 +
        1070449264324448178078715136777499277835829410408785305942192839574596) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (281 - x)) = _
  rw [show 282 = 99 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 2 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (282 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_282 :
    recurrence4B3A3.coeff 282 =
      (((49031773633884792131835172574 * 10 ^ 70 +
        7454786701153031625403563860699162773246916175170811686368867488296252) * 10 ^ 70 +
        3041837531041888075027175934168485101258264203697113873993999471617251) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (282 - x)) = _
  rw [show 283 = 100 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 1 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (283 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_283 :
    recurrence4B3A3.coeff 283 =
      -(((16978750780142487890119737826 * 10 ^ 70 +
        0720901926555055758829143557725270029240180294182084290913288632108050) * 10 ^ 70 +
        4293809757832141302902741395482247706464040242046966311080045081270291) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (283 - x)) = _
  rw [show 284 = 101 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (284 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_284 :
    recurrence4B3A3.coeff 284 =
      (((5526842971956288697142434053 * 10 ^ 70 +
        8569973776412740312385409982023582807410943730304274362747837814448506) * 10 ^ 70 +
        8044970602600506499891346933016253273795549931567798039268871369546909) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (284 - x)) = _
  rw [show 285 = 102 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 31 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (285 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_285 :
    recurrence4B3A3.coeff 285 =
      -(((1685606205006759946960790779 * 10 ^ 70 +
        4218867824196998946947767262050240663511676631514378027382519343780279) * 10 ^ 70 +
        9386792345057666886504606019726924097576680070135560231390144846147590) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (285 - x)) = _
  rw [show 286 = 103 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 30 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (286 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_286 :
    recurrence4B3A3.coeff 286 =
      (((478955227310155733241131323 * 10 ^ 70 +
        7172297284239046692392327528609962012712645648550711403420907004687714) * 10 ^ 70 +
        3940198073388137765520109405860044411877002591683946503767859610189159) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (286 - x)) = _
  rw [show 287 = 104 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 29 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (287 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_287 :
    recurrence4B3A3.coeff 287 =
      -(((125709655530770064706833005 * 10 ^ 70 +
        3490715603479332490538587187558571837112261798616703308644435780844321) * 10 ^ 70 +
        0046386678468713309637799838077092320801128109939715597694704142069848) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (287 - x)) = _
  rw [show 288 = 105 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 28 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (288 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_288 :
    recurrence4B3A3.coeff 288 =
      (((30066174556095157827243164 * 10 ^ 70 +
        7815569250913873012062614953916381949550821820039958577660321790998972) * 10 ^ 70 +
        9174081438140080194781560108797129404114080645833170059728055185882545) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (288 - x)) = _
  rw [show 289 = 106 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 27 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (289 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_289 :
    recurrence4B3A3.coeff 289 =
      -(((6396769395637929617154799 * 10 ^ 70 +
        4054541302359559238336997338798252960016243702243017246587611196711258) * 10 ^ 70 +
        4916431666051763183123924191976475984273789705999791196404551918605344) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (289 - x)) = _
  rw [show 290 = 107 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 26 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (290 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_290 :
    recurrence4B3A3.coeff 290 =
      (((1149855075532106373516040 * 10 ^ 70 +
        4116231966957138585357307762417312344701604172279026162432603749489475) * 10 ^ 70 +
        2868756569194190615448928419156656566254246937429596290460986620536581) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (290 - x)) = _
  rw [show 291 = 108 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 25 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (291 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_291 :
    recurrence4B3A3.coeff 291 =
      -(((149492074201183622626066 * 10 ^ 70 +
        7092673970349745060612034193432626500298481088107006303383143081567518) * 10 ^ 70 +
        4285457614298897929220476327952912565513967774449908198556546312991054) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (291 - x)) = _
  rw [show 292 = 109 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 24 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (292 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_292 :
    recurrence4B3A3.coeff 292 =
      (((2310863282441633168343 * 10 ^ 70 +
        5097995218192528181573689083502830314371505372323888962229542278053170) * 10 ^ 70 +
        1156912850446579355231826632400343669061269185446656961972967925633931) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (292 - x)) = _
  rw [show 293 = 110 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 23 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (293 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_293 :
    recurrence4B3A3.coeff 293 =
      (((6844578954536399796171 * 10 ^ 70 +
        6925907995225189375411758483674778964318883670176607919924697107454371) * 10 ^ 70 +
        8378479116060402428801027098280737070398018451357885423415691289066869) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (293 - x)) = _
  rw [show 294 = 111 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 22 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (294 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_294 :
    recurrence4B3A3.coeff 294 =
      -(((2956069200742632456701 * 10 ^ 70 +
        2147764307613124254444039858617045863883342978850775216297496817613031) * 10 ^ 70 +
        5841735085765825622915159570975109207479414320795764221526823765111214) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (294 - x)) = _
  rw [show 295 = 112 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 21 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (295 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_295 :
    recurrence4B3A3.coeff 295 =
      (((870463065307669976209 * 10 ^ 70 +
        9924430033750371947490872649364115957609363990778996431765871283925917) * 10 ^ 70 +
        6870985715470045270258853762957585820397381655631213666758576294845962) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (295 - x)) = _
  rw [show 296 = 113 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 20 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (296 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_296 :
    recurrence4B3A3.coeff 296 =
      -(((209872530106294757837 * 10 ^ 70 +
        9508733645923161354756432881216644717124154641033818686188618474267640) * 10 ^ 70 +
        5110145524214885722985553024847240506109532426575008730504772331571607) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (296 - x)) = _
  rw [show 297 = 114 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 19 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (297 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_297 :
    recurrence4B3A3.coeff 297 =
      (((43516867137414699092 * 10 ^ 70 +
        3167129813217262308436733305191692792148502684136719213449845843121985) * 10 ^ 70 +
        7017136040254022174678727506478562807393863338948378660822320631526181) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (297 - x)) = _
  rw [show 298 = 115 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 18 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (298 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_298 :
    recurrence4B3A3.coeff 298 =
      -(((7866253970758043417 * 10 ^ 70 +
        1799269104689798149037990025698064781859136744944736599495809267643557) * 10 ^ 70 +
        3969200786285292168444630464988156043496344409129462665128293108177167) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (298 - x)) = _
  rw [show 299 = 116 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 17 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (299 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_299 :
    recurrence4B3A3.coeff 299 =
      (((1233903994902497876 * 10 ^ 70 +
        2200949330310554560123335973404324361199910170726345507067738412404599) * 10 ^ 70 +
        4354936693994909323612160624056089242541212241680219342610653274844897) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (299 - x)) = _
  rw [show 300 = 117 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 16 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (300 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_300 :
    recurrence4B3A3.coeff 300 =
      -(((163988216554949817 * 10 ^ 70 +
        7964662426214741568124438932673535959171430755294027278630207733805385) * 10 ^ 70 +
        2654800770372968718797656712696447174099893601045529716210971809486967) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (300 - x)) = _
  rw [show 301 = 118 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 15 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (301 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_301 :
    recurrence4B3A3.coeff 301 =
      (((17302811959230617 * 10 ^ 70 +
        3894058452425437158367066360170527996863967229047720962562189218292499) * 10 ^ 70 +
        4549702522998601085762099844005158194248926024238317779875767144768401) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (301 - x)) = _
  rw [show 302 = 119 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 14 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (302 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_302 :
    recurrence4B3A3.coeff 302 =
      -(((1143697874910713 * 10 ^ 70 +
        6961772480468243862613104142830179591142036128080228182474243386491921) * 10 ^ 70 +
        7235862396504512062945989919835827551131423260547023664347101947967249) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (302 - x)) = _
  rw [show 303 = 120 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 13 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (303 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_303 :
    recurrence4B3A3.coeff 303 =
      -(((39295102318857 * 10 ^ 70 +
        9992680937142435765781366218922630690955520077741894351317769929803997) * 10 ^ 70 +
        1690159937192549586444237592428039360600414417553110369042186070434024) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (303 - x)) = _
  rw [show 304 = 121 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 12 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (304 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_304 :
    recurrence4B3A3.coeff 304 =
      (((27991659528431 * 10 ^ 70 +
        2888596701217408354133141710232438641022667867666763285905441413656586) * 10 ^ 70 +
        4513527522427673216788378706273016369345849204745451416026700147501060) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (304 - x)) = _
  rw [show 305 = 122 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 11 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (305 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_305 :
    recurrence4B3A3.coeff 305 =
      -(((5448650536836 * 10 ^ 70 +
        5972417674086851264059059431640001481936400607469313418183315756684390) * 10 ^ 70 +
        8080739776317967253156821909674125634979532845884868504528015646102053) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (305 - x)) = _
  rw [show 306 = 123 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 10 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (306 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_306 :
    recurrence4B3A3.coeff 306 =
      (((727971978323 * 10 ^ 70 +
        6508392178501471832604505405032515649747854927909989323056868229341904) * 10 ^ 70 +
        1420052777402634375950724648765213686586369607387258019826775821705251) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (306 - x)) = _
  rw [show 307 = 124 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 9 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (307 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_307 :
    recurrence4B3A3.coeff 307 =
      -(((73066202703 * 10 ^ 70 +
        2856636195979743732789888768640893069461042326915435148111306088134810) * 10 ^ 70 +
        8536465098498926588670274543134803354826655738492801095572266172370193) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (307 - x)) = _
  rw [show 308 = 125 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 8 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (308 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_308 :
    recurrence4B3A3.coeff 308 =
      (((5296178052 * 10 ^ 70 +
        9208862000220236101772512738676544777532709762259015995377642046828864) * 10 ^ 70 +
        1773118394559484636539528732473897541113505688387358090306667430526649) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (308 - x)) = _
  rw [show 309 = 126 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 7 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (309 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_309 :
    recurrence4B3A3.coeff 309 =
      -(((209026623 * 10 ^ 70 +
        9837187814469460978081572231658942296423526286412745437169449597844258) * 10 ^ 70 +
        5652777586221937589372208864760764834447375594920394554024591131053420) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (309 - x)) = _
  rw [show 310 = 127 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 6 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
