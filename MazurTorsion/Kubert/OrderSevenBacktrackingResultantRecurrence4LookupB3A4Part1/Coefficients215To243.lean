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

private theorem recurrence4B3A4_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (215 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_215 :
    recurrence4B3A4.coeff 215 =
      (((3770324010414482394605607206693775689482175796570686306 * 10 ^ 70 +
        9304077907664459136996933734967950917967890754219958556015972096945733) * 10 ^ 70 +
        4966223572402946692803511558652005847955143799076062743257320483835823) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (215 - x)) = _
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
  rw [recurrence4B3A4_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (216 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_216 :
    recurrence4B3A4.coeff 216 =
      -(((2141434079224488700196839234250482627391651614728182333 * 10 ^ 70 +
        4210442631945286677054238498267153511733785475703037508034467705823201) * 10 ^ 70 +
        2249908410992908030445268013331794146802877902092623771332597824449157) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (216 - x)) = _
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
    rw [show 83 = 31 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (217 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_217 :
    recurrence4B3A4.coeff 217 =
      (((1177550720678007035539802055396557833588369168602277117 * 10 ^ 70 +
        9142634744387247853617783601016358597571151277101264430382113323833480) * 10 ^ 70 +
        7112761609514111641378193044626670611388840016702081090083579827011249) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (217 - x)) = _
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
    rw [show 83 = 30 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (218 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_218 :
    recurrence4B3A4.coeff 218 =
      -(((628683798726464555826301988997049047467538349216823989 * 10 ^ 70 +
        6860665507572520392170453875360290423991534558673513893633746523553301) * 10 ^ 70 +
        4766016338623736774313600827619641360803706660950186566651532072263408) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (218 - x)) = _
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
    rw [show 83 = 29 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (219 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_219 :
    recurrence4B3A4.coeff 219 =
      (((326493515920423383329401119239351109865492872645792815 * 10 ^ 70 +
        9049901257275270426983121417359998039112847241681357198340146419348873) * 10 ^ 70 +
        1867159062048582136287818796896403858067381456509159407615206026473837) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (219 - x)) = _
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
    rw [show 83 = 28 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (220 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_220 :
    recurrence4B3A4.coeff 220 =
      -(((165135489506849765689195349421830644590086504744769665 * 10 ^ 70 +
        0632981548201829867690153002157969043096833304138552310040363808131482) * 10 ^ 70 +
        8524830134513143009296330119023229901028999005315906239676860080625749) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (220 - x)) = _
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
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (221 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_221 :
    recurrence4B3A4.coeff 221 =
      (((81408551780288236608899451600179489078765343881058879 * 10 ^ 70 +
        9056655992819184088733996926903870201488680969451011169399933529399010) * 10 ^ 70 +
        5391975687847332549650699477382945102202774315769135888033655968872739) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (221 - x)) = _
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
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (222 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_222 :
    recurrence4B3A4.coeff 222 =
      -(((39134812916039723448618068652280018965907495517521079 * 10 ^ 70 +
        5462319893815952238049706960184397939683593874041725489001006960540319) * 10 ^ 70 +
        5355801489493785644588522836378125254234879264458391952765169216411575) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (222 - x)) = _
  rw [show 223 = 44 +
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
    rw [show 83 = 25 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (223 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_223 :
    recurrence4B3A4.coeff 223 =
      (((18349085625116822598632979276718405373939699595380766 * 10 ^ 70 +
        9594769007552443566549150356528170676674697807487655407385525506228171) * 10 ^ 70 +
        5747197915593462636304126770245148097838452835787579429900252269190811) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (223 - x)) = _
  rw [show 224 = 45 +
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
    rw [show 83 = 24 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (224 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_224 :
    recurrence4B3A4.coeff 224 =
      -(((8391408502738952623237583230273992620193637200229313 * 10 ^ 70 +
        6560244404235765719285934113504872591059770642433154465227223390988063) * 10 ^ 70 +
        1251240229820587339115260176557311692231032719561067059863182116787146) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (224 - x)) = _
  rw [show 225 = 46 +
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
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (225 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_225 :
    recurrence4B3A4.coeff 225 =
      (((3742542602164913099405571370207731549392688006202295 * 10 ^ 70 +
        0358535616319257944665084661421524985966100771601492055386748644052104) * 10 ^ 70 +
        4324325268886477747801595409849318777297705129503277082216384026085689) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (225 - x)) = _
  rw [show 226 = 47 +
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
    rw [show 83 = 22 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (226 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_226 :
    recurrence4B3A4.coeff 226 =
      -(((1627382496302569908164018386758005220644436628935888 * 10 ^ 70 +
        3341632162225343231811335896311308822900314416415805992160887099485548) * 10 ^ 70 +
        7330282786592052657075520380297724519589606716801215541603593019366017) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (226 - x)) = _
  rw [show 227 = 48 +
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
    rw [show 83 = 21 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (227 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_227 :
    recurrence4B3A4.coeff 227 =
      (((689635521136473298420415796672665636019513283131254 * 10 ^ 70 +
        3791955013790535874900956556432603670575193110447858479881288522374302) * 10 ^ 70 +
        4515600958053277450012138205625000583849261282408699452993452178909417) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (227 - x)) = _
  rw [show 228 = 49 +
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
    rw [show 83 = 20 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (228 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_228 :
    recurrence4B3A4.coeff 228 =
      -(((284642329490514214419881844783527372685653112457703 * 10 ^ 70 +
        5590079411717689805949441472605024224324737786077674111927583112287746) * 10 ^ 70 +
        9658536150316790605039610504827781788887184643125441400990871499406656) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (228 - x)) = _
  rw [show 229 = 50 +
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
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (229 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_229 :
    recurrence4B3A4.coeff 229 =
      (((114334065615575088775822813463232306025695510196876 * 10 ^ 70 +
        3905128801643297841434429541578381997831304541979434084832042617392166) * 10 ^ 70 +
        9989066042934616148887404405940293358319815936935087761719643514107289) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (229 - x)) = _
  rw [show 230 = 51 +
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
    rw [show 83 = 18 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (230 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_230 :
    recurrence4B3A4.coeff 230 =
      -(((44643016072769947198177701076031410100426462749868 * 10 ^ 70 +
        1872382830490867840469839086776002840165594881740079698704859362651269) * 10 ^ 70 +
        6496064899626966110677794814006509054065081551645607890600378303760629) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (230 - x)) = _
  rw [show 231 = 52 +
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
    rw [show 83 = 17 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (231 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_231 :
    recurrence4B3A4.coeff 231 =
      (((16916669219394716427114725657616641084502469227433 * 10 ^ 70 +
        1032730901111136213196194243804001699536070513779908344021848300304900) * 10 ^ 70 +
        9012266038941331621300756762118196597340042406719909525238335898124759) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (231 - x)) = _
  rw [show 232 = 53 +
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
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (232 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_232 :
    recurrence4B3A4.coeff 232 =
      -(((6205312619522838812155017779979557648473768579295 * 10 ^ 70 +
        2560289991034355838782929064833998200617059796483827579563104796257907) * 10 ^ 70 +
        3388781098266069550399175448695281652135895655992788350412200279063618) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (232 - x)) = _
  rw [show 233 = 54 +
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
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (233 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_233 :
    recurrence4B3A4.coeff 233 =
      (((2194470732930217390793831885133634618593701774787 * 10 ^ 70 +
        6150686978909108980945438881767134133213411491554192523756662053297155) * 10 ^ 70 +
        7421336793822055137488523678995184421499190225318550606243015098606767) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (233 - x)) = _
  rw [show 234 = 55 +
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
    rw [show 83 = 14 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (234 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_234 :
    recurrence4B3A4.coeff 234 =
      -(((742956351742455866914883720419847353155459633057 * 10 ^ 70 +
        1574081118247632059381815788641846187804462950740498867574576725694843) * 10 ^ 70 +
        8421972673162484689107969243254832915953057524134529581290796275918857) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (234 - x)) = _
  rw [show 235 = 56 +
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
    rw [show 83 = 13 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (235 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_235 :
    recurrence4B3A4.coeff 235 =
      (((237670251548326237554824663278674152897308338539 * 10 ^ 70 +
        7511877192062227131941522778750779292617477459236614020186294755576280) * 10 ^ 70 +
        7362141446753196677661554614247736718808422458066808477856346972124299) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (235 - x)) = _
  rw [show 236 = 57 +
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
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (236 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_236 :
    recurrence4B3A4.coeff 236 =
      -(((69900772882398023876259060639981817914314420275 * 10 ^ 70 +
        9352731838494624210487203993276730946239814558509498579945849202314138) * 10 ^ 70 +
        1136271457838317971291789887269647445735634134712722542047913601015113) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (236 - x)) = _
  rw [show 237 = 58 +
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
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (237 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_237 :
    recurrence4B3A4.coeff 237 =
      (((17634411224586505481821186400947269089243224052 * 10 ^ 70 +
        9399779076619254152560701953058020331971525072718930082358432192074730) * 10 ^ 70 +
        9563078482275375138891120800878603687230754197759281296628379785636792) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (237 - x)) = _
  rw [show 238 = 59 +
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
    rw [show 83 = 10 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (238 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_238 :
    recurrence4B3A4.coeff 238 =
      -(((2901719333853415664958238203303817843663639290 * 10 ^ 70 +
        3621849534855684169559241490615138579626142732120240059507520881035351) * 10 ^ 70 +
        2665186925536466450509991088924284585226205684908179835508929482644634) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (238 - x)) = _
  rw [show 239 = 60 +
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
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (239 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_239 :
    recurrence4B3A4.coeff 239 =
      -(((488698472707462977139141176606152325472304899 * 10 ^ 70 +
        8922878731555023203251573459304463769585139858128241319107541369926646) * 10 ^ 70 +
        0101428321452953562596409401393036473146495787298572933163779867168885) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (239 - x)) = _
  rw [show 240 = 61 +
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
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (240 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_240 :
    recurrence4B3A4.coeff 240 =
      (((846159528111470900882588147007742439019417421 * 10 ^ 70 +
        0321604408056984640985346570274722504204481527096306036900774178156828) * 10 ^ 70 +
        5355320004698262334941533648113231242773354423144389479925224012498015) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (240 - x)) = _
  rw [show 241 = 62 +
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
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (241 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_241 :
    recurrence4B3A4.coeff 241 =
      -(((593677558988642642816548245138501603600544749 * 10 ^ 70 +
        5094034130682679730449817381738533632661942360316433855875804064676502) * 10 ^ 70 +
        4271907357038119017894442907753471810858643055786310875620582451984848) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (241 - x)) = _
  rw [show 242 = 63 +
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
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (242 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_242 :
    recurrence4B3A4.coeff 242 =
      (((336606784232475865146522119934117283445205532 * 10 ^ 70 +
        6493184924265900069025355559199975043691664085645874399220739024952480) * 10 ^ 70 +
        8155487836006336552803241714180121998702071969532682207498067285944880) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (242 - x)) = _
  rw [show 243 = 64 +
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
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (243 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_243 :
    recurrence4B3A4.coeff 243 =
      -(((172415488000386052670594905194775024547229253 * 10 ^ 70 +
        0916562843595861073819118362784232144965526569796081496104300723316531) * 10 ^ 70 +
        4841071206339108733307271403407476498544194077967618624246248368258520) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (243 - x)) = _
  rw [show 244 = 65 +
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
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
