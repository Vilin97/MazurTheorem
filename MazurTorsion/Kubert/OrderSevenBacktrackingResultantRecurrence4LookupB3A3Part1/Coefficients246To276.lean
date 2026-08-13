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

private theorem recurrence4B3A3_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (246 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_246 :
    recurrence4B3A3.coeff 246 =
      -(((88048845557248867395106520396560455691262021 * 10 ^ 70 +
        7504760851457590003001033044000290593775652385443777228611689307696016) * 10 ^ 70 +
        6412043713851997188802989158382348924577685195588969849153634011943502) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (246 - x)) = _
  rw [show 247 = 64 +
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
    rw [show 87 = 5 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (247 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_247 :
    recurrence4B3A3.coeff 247 =
      (((21068484634900988552700135887803821771533763 * 10 ^ 70 +
        4959662422130886036273834312881115206326143289991457412626133747907110) * 10 ^ 70 +
        3422228894036770445996198708623092258624748960000945307781859988971031) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (247 - x)) = _
  rw [show 248 = 65 +
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
    rw [show 87 = 4 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (248 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_248 :
    recurrence4B3A3.coeff 248 =
      -(((4181685818370386685379556227330320506754779 * 10 ^ 70 +
        6238537126873161797850552037188058337459721910090167233672776697470233) * 10 ^ 70 +
        8454098023015155467180047116660308603815193399779785826366077255270663) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (248 - x)) = _
  rw [show 249 = 66 +
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
    rw [show 87 = 3 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (249 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_249 :
    recurrence4B3A3.coeff 249 =
      -(((122074967361057878802022131828935956821160 * 10 ^ 70 +
        1700001121976180904668410829149318427009118667132706343212680142599319) * 10 ^ 70 +
        7987876352999312351460735634463319562475158410654430885536655352808173) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (249 - x)) = _
  rw [show 250 = 67 +
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
    rw [show 87 = 2 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (250 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_250 :
    recurrence4B3A3.coeff 250 =
      (((990223379651402706379343898773149363192590 * 10 ^ 70 +
        7867012227552091946231734805017406099981170925405570131770520236234588) * 10 ^ 70 +
        4543479011350823615768126496843220712771259182336256734476020419164481) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (250 - x)) = _
  rw [show 251 = 68 +
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
    rw [show 87 = 1 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (251 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_251 :
    recurrence4B3A3.coeff 251 =
      -(((894960685253512527205731505035679184670107 * 10 ^ 70 +
        9659403248592416819073302786306731150279768565884575348430460318266470) * 10 ^ 70 +
        5411363168273020012848109951995674625265707403352609759780097131222745) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (251 - x)) = _
  rw [show 252 = 69 +
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
  rw [recurrence4B3A3_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (252 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_252 :
    recurrence4B3A3.coeff 252 =
      (((601939974285942643279486315184508408631357 * 10 ^ 70 +
        4757687675843690085467646296985015314918475091197001876821814175462268) * 10 ^ 70 +
        8590445229384010325283206079757340607438747629740773211666309205008203) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (252 - x)) = _
  rw [show 253 = 70 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 31 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (253 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_253 :
    recurrence4B3A3.coeff 253 =
      -(((347864950872002107560509230721819852821526 * 10 ^ 70 +
        0971783173299648908701696134294192633636621808148013782428143785864660) * 10 ^ 70 +
        0343200926596026698853901972842339184180742373275844451413642672189097) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (253 - x)) = _
  rw [show 254 = 71 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 30 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (254 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_254 :
    recurrence4B3A3.coeff 254 =
      (((180615682424410717740851222259952086302876 * 10 ^ 70 +
        5161731303119725190850478896802797188327305595686862771519855001207750) * 10 ^ 70 +
        5945309818479601527484401003080701106785963285262618495274929973425338) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (254 - x)) = _
  rw [show 255 = 72 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 29 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (255 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_255 :
    recurrence4B3A3.coeff 255 =
      -(((85910129753670993294956658337310638843009 * 10 ^ 70 +
        8904124028768948420232835191127542140054241908317616670008040806546887) * 10 ^ 70 +
        8173120215503495938017156527472720780499112277299716162074398903521380) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (255 - x)) = _
  rw [show 256 = 73 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 28 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (256 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_256 :
    recurrence4B3A3.coeff 256 =
      (((37789302759998989735055966864623770552239 * 10 ^ 70 +
        5832667376343204968817623640406459726841729693594054794778625628150126) * 10 ^ 70 +
        1743386791460258800431543187988364489521417805752474352001619577414937) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (256 - x)) = _
  rw [show 257 = 74 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 27 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (257 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_257 :
    recurrence4B3A3.coeff 257 =
      -(((15430518879791395846336510255634765956958 * 10 ^ 70 +
        3109851235990820027031827920229105779580185443811514137472372319280893) * 10 ^ 70 +
        7117589629814774449752211253135493244734328139101044599499422704909266) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (257 - x)) = _
  rw [show 258 = 75 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (258 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_258 :
    recurrence4B3A3.coeff 258 =
      (((5845733017717549002132196376234109612666 * 10 ^ 70 +
        3996198195800314906450936225405913296386303632031258122195694893015530) * 10 ^ 70 +
        5196179940127259127715276988372657786438643863457116565087683840742853) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (258 - x)) = _
  rw [show 259 = 76 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 25 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (259 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_259 :
    recurrence4B3A3.coeff 259 =
      -(((2043751739092822268139404012902393804160 * 10 ^ 70 +
        4038813304263851120369092803551841836678890625722697459167150103026362) * 10 ^ 70 +
        2084184994049502417196773160671549709827408624851471127197098730661494) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (259 - x)) = _
  rw [show 260 = 77 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 24 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (260 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_260 :
    recurrence4B3A3.coeff 260 =
      (((651121864650145123551268336931765996857 * 10 ^ 70 +
        5966944278714161126269375134328633803565558549136339122979733345230933) * 10 ^ 70 +
        5398787235056839692213375516723818070259875259115444231241770587986649) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (260 - x)) = _
  rw [show 261 = 78 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 23 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (261 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_261 :
    recurrence4B3A3.coeff 261 =
      -(((183897938625094488592552427421583356366 * 10 ^ 70 +
        8737166817011117336064785207201218089675185193866337081586782294972088) * 10 ^ 70 +
        0782605168368075481953428565592697179618175875602314155178063576089106) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (261 - x)) = _
  rw [show 262 = 79 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 22 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (262 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_262 :
    recurrence4B3A3.coeff 262 =
      (((42966529614151053276834659905490334207 * 10 ^ 70 +
        4732030517502292654128717950704233347126972469539352274262588243356006) * 10 ^ 70 +
        2332768690559718867963005877079818132543511115993720246307806050074367) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (262 - x)) = _
  rw [show 263 = 80 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 21 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (263 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_263 :
    recurrence4B3A3.coeff 263 =
      -(((6360054921462236715918768354647687098 * 10 ^ 70 +
        2430816437963330154179259222183613219603306293359380653689247638217316) * 10 ^ 70 +
        3328482197390832441674198676165765467862631248080663353900194931209872) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (263 - x)) = _
  rw [show 264 = 81 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 20 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (264 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_264 :
    recurrence4B3A3.coeff 264 =
      -(((840954610983212693243459807136790203 * 10 ^ 70 +
        2400354269100047795050455365946230361784619569227042425477702247071742) * 10 ^ 70 +
        3913738463039541010839901531785100207067714028226231360401802037451140) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (264 - x)) = _
  rw [show 265 = 82 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 19 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (265 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_265 :
    recurrence4B3A3.coeff 265 =
      (((1247466541255782752335306755868728320 * 10 ^ 70 +
        3789076938668778708808530826905104761677762616847006442575391870272776) * 10 ^ 70 +
        8001789772589512625329286234086517090993087594521189700033763051897537) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (265 - x)) = _
  rw [show 266 = 83 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 18 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (266 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_266 :
    recurrence4B3A3.coeff 266 =
      -(((693287335134881302636021205815258568 * 10 ^ 70 +
        5401199194826700888087156944273777718513072052087523626388231159853931) * 10 ^ 70 +
        7330536769891477760699445337420513994550549061788610773214416266743733) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (266 - x)) = _
  rw [show 267 = 84 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 17 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (267 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_267 :
    recurrence4B3A3.coeff 267 =
      (((299277040830515408331918564802901810 * 10 ^ 70 +
        1960495163585424676868721624978003856519485540530228576973286096438941) * 10 ^ 70 +
        4284006077933859989556481920724815955803521596707802569709854098802394) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (267 - x)) = _
  rw [show 268 = 85 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (268 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_268 :
    recurrence4B3A3.coeff 268 =
      -(((112922845375157998792912945366708568 * 10 ^ 70 +
        4348213440159377954191089028620814112469200425490369554768784065356963) * 10 ^ 70 +
        5337574266519676230878618897996826534726578177634309387837151180243529) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (268 - x)) = _
  rw [show 269 = 86 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 15 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (269 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_269 :
    recurrence4B3A3.coeff 269 =
      (((38897795821580566894715474569928129 * 10 ^ 70 +
        1493760661114442269956631592069390166985952457060380154842818497881110) * 10 ^ 70 +
        8865539383862293134914300655071865324654763884991602823659198829983752) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (269 - x)) = _
  rw [show 270 = 87 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 14 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (270 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_270 :
    recurrence4B3A3.coeff 270 =
      -(((12485369723524815557751417806573370 * 10 ^ 70 +
        3495795365563065046161937268763840887430998058654676451576979873232755) * 10 ^ 70 +
        4971959389573421258618125298965607254889933784028207981242704807372640) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (270 - x)) = _
  rw [show 271 = 88 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 13 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (271 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_271 :
    recurrence4B3A3.coeff 271 =
      (((3763572309804020607700146274424904 * 10 ^ 70 +
        3883993229941639419258929694532114855045231988187284186774578237344117) * 10 ^ 70 +
        3387336490128793388041678104436034651178163658364620742251117329916830) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (271 - x)) = _
  rw [show 272 = 89 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 12 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (272 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_272 :
    recurrence4B3A3.coeff 272 =
      -(((1059075060385397026671362408870924 * 10 ^ 70 +
        3322016351961455078192194187664732052987527725745176494159661875962770) * 10 ^ 70 +
        8971145515391045171438345420194827526040062759278698875464643880647782) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (272 - x)) = _
  rw [show 273 = 90 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 11 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (273 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_273 :
    recurrence4B3A3.coeff 273 =
      (((269686052953525261448358107268726 * 10 ^ 70 +
        3442232382267099517818791802857601940925070286053714007334462980351501) * 10 ^ 70 +
        2742848378259115599400032687866436455161088122713626896672005603921210) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (273 - x)) = _
  rw [show 274 = 91 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 10 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (274 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_274 :
    recurrence4B3A3.coeff 274 =
      -(((56086369835499634535042326725139 * 10 ^ 70 +
        1976659834794102292690843377747188249928126712877619690669967912171399) * 10 ^ 70 +
        2449096976933691659721360537579033076413464101260443279367752285652970) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (274 - x)) = _
  rw [show 275 = 92 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 9 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (275 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_275 :
    recurrence4B3A3.coeff 275 =
      (((5307732595295931689509770643553 * 10 ^ 70 +
        1461229917116865587042240018139331474517746249178967814874480321695155) * 10 ^ 70 +
        3769146507710776156274493225932204842876058177437240002744469830185693) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (275 - x)) = _
  rw [show 276 = 93 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 8 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A3_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A3_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A3_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient3.coeff (276 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A3_coeff_276 :
    recurrence4B3A3.coeff 276 =
      (((3401887042338899462273667791239 * 10 ^ 70 +
        2985501339375769786785735953826076542719930201626168124863767993405918) * 10 ^ 70 +
        1396201550790625163220462226845337414740458368546156513427310152855247) : ℚ) := by
  unfold recurrence4B3A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient3.coeff x * remainder4Coefficient3.coeff (276 - x)) = _
  rw [show 277 = 94 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 7 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A3_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A3_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
