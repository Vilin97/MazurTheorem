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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (244 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_244 :
    recurrence4B3A4.coeff 244 =
      (((82859251955136728534456300876436220527113651 * 10 ^ 70 +
        4295256671755794848285049803963402104410146267740004223965982064786190) * 10 ^ 70 +
        3572057718729915177137060095163215499535037596159723663075199597947595) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (244 - x)) = _
  rw [show 245 = 66 +
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
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (245 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_245 :
    recurrence4B3A4.coeff 245 =
      -(((37953130188619760892070608068176147664607889 * 10 ^ 70 +
        9237706415130664274812731180750890957009411791427596125386802381492405) * 10 ^ 70 +
        7163895844846739682761295069946279900992997558609334680856294103953893) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (245 - x)) = _
  rw [show 246 = 67 +
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
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (246 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_246 :
    recurrence4B3A4.coeff 246 =
      (((16678500643657198443949427357161917478966530 * 10 ^ 70 +
        1123040529097114875722062667848068783787049801251166602693525727355385) * 10 ^ 70 +
        9233620841607286679946419039218775464721141252168634172721765891409406) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (246 - x)) = _
  rw [show 247 = 68 +
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
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (247 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_247 :
    recurrence4B3A4.coeff 247 =
      -(((7046114101947233054185195723590046303730814 * 10 ^ 70 +
        9104933129349908133330354203999122475874542522227970968485206976754358) * 10 ^ 70 +
        4735228865006975405676867620573093219808005269054535808952969176859586) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (247 - x)) = _
  rw [show 248 = 69 +
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
  rw [recurrence4B3A4_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (248 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_248 :
    recurrence4B3A4.coeff 248 =
      (((2859876230185277107635665387895054347555766 * 10 ^ 70 +
        5601666309683313715481244640997599116108099744598183326488624404479045) * 10 ^ 70 +
        3055860818143613898623423704487079945882597750771708714367336735680571) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (248 - x)) = _
  rw [show 249 = 70 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (249 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_249 :
    recurrence4B3A4.coeff 249 =
      -(((1112339485244252217870210898937255895815218 * 10 ^ 70 +
        6860675429961399816187529545576698523620012139044337529770275832702321) * 10 ^ 70 +
        0852988519196705561193579058394487904450835219878410986834007944363941) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (249 - x)) = _
  rw [show 250 = 71 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (250 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_250 :
    recurrence4B3A4.coeff 250 =
      (((412769561635244863083470177879907136386389 * 10 ^ 70 +
        1385470884820471708458155024321999921563590141572183598653278029799077) * 10 ^ 70 +
        8538413679080417336561640928192668659329081572714995924918897379154648) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (250 - x)) = _
  rw [show 251 = 72 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (251 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_251 :
    recurrence4B3A4.coeff 251 =
      -(((145147638914417912396386477958197861774146 * 10 ^ 70 +
        9714443546232852409880937509091958975757990245289767478503695100885906) * 10 ^ 70 +
        3424628757005447334541296356533500808408887992106525220067377791588200) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (251 - x)) = _
  rw [show 252 = 73 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (252 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_252 :
    recurrence4B3A4.coeff 252 =
      (((47852557575069867672715422126623753458131 * 10 ^ 70 +
        3565075856462395733756075275454646901366123675192834139111490264510967) * 10 ^ 70 +
        2846878691374671032221325482997197310332876301572963101524345465038164) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (252 - x)) = _
  rw [show 253 = 74 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (253 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_253 :
    recurrence4B3A4.coeff 253 =
      -(((14523039562892106753840802431440909887576 * 10 ^ 70 +
        4931734875080869336613536396459281361769297398046085539357330933259024) * 10 ^ 70 +
        6008043212665000499992256479259083422756241396998791420521491090646637) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (253 - x)) = _
  rw [show 254 = 75 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (254 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_254 :
    recurrence4B3A4.coeff 254 =
      (((3913600683243822999621046547869642313590 * 10 ^ 70 +
        0441266457746992613052103919145585890216382479851056554126366622862000) * 10 ^ 70 +
        2055429294424460797249135581637071404271056633663734299402454821371100) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (254 - x)) = _
  rw [show 255 = 76 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (255 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_255 :
    recurrence4B3A4.coeff 255 =
      -(((854074929819220648436357170412000253644 * 10 ^ 70 +
        0132130281082424238955597423431716799435412516557392745092249845947355) * 10 ^ 70 +
        5059253802774043284961958886406372861627963656241860301704670061019709) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (255 - x)) = _
  rw [show 256 = 77 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (256 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_256 :
    recurrence4B3A4.coeff 256 =
      (((98323794769780094649407919126535556209 * 10 ^ 70 +
        8332773210371804175671109384813709269757461544545365351103660088946949) * 10 ^ 70 +
        4220279747444879178447679138061187223767604267975688811123337336279938) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (256 - x)) = _
  rw [show 257 = 78 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (257 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_257 :
    recurrence4B3A4.coeff 257 =
      (((35387900189656742631531095895309703548 * 10 ^ 70 +
        6145975739200543878708550897098747440692352260523722530648518833981103) * 10 ^ 70 +
        2415988002469810010815878939246797055509977274221303359918856717933258) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (257 - x)) = _
  rw [show 258 = 79 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (258 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_258 :
    recurrence4B3A4.coeff 258 =
      -(((33984553059933006813851853946006419723 * 10 ^ 70 +
        8598764251792963245065311901107146799190373331628988841060069340609447) * 10 ^ 70 +
        6956781345691076472303729552669785557030985735254239004878318155330408) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (258 - x)) = _
  rw [show 259 = 80 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (259 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_259 :
    recurrence4B3A4.coeff 259 =
      (((17661128696825722373022603221584663505 * 10 ^ 70 +
        9619091298715722999618056415866827636630470256571259981610800917174880) * 10 ^ 70 +
        5360263576705260111736521879500210183749807861143572038073188521635495) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (259 - x)) = _
  rw [show 260 = 81 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (260 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_260 :
    recurrence4B3A4.coeff 260 =
      -(((7389912004866915635843495409019366006 * 10 ^ 70 +
        9248185954176430784551660180257775749412734975089546322226049154798834) * 10 ^ 70 +
        8803350802096386064400195783654284875418347876755731976395412747582332) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (260 - x)) = _
  rw [show 261 = 82 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (261 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_261 :
    recurrence4B3A4.coeff 261 =
      (((2706429516472781261514012931465764621 * 10 ^ 70 +
        3120691282153534062198724972431774818231217842393798138639890837706507) * 10 ^ 70 +
        8398910898165139302755454766891663605905679683982292886325159347872540) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (261 - x)) = _
  rw [show 262 = 83 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (262 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_262 :
    recurrence4B3A4.coeff 262 =
      -(((891547097249974456580452858326760272 * 10 ^ 70 +
        3182011402201796782987138085967075973649595913443656538556096875230349) * 10 ^ 70 +
        0189855106431831841137802653190035743168031373964866248714288025880322) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (262 - x)) = _
  rw [show 263 = 84 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (263 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_263 :
    recurrence4B3A4.coeff 263 =
      (((265325287834601844471981242958785470 * 10 ^ 70 +
        7068715653469948226148395917369153463348870412724803098871995594681184) * 10 ^ 70 +
        3593621969315663272248678779432515640737432931707905673752944215322255) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (263 - x)) = _
  rw [show 264 = 85 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (264 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_264 :
    recurrence4B3A4.coeff 264 =
      -(((70122606754248824932310425367104530 * 10 ^ 70 +
        2199887411873968221205773533959916927800783939788588049278678678205515) * 10 ^ 70 +
        9699508063357805085699785392889110054666502325139658511348284421395356) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (264 - x)) = _
  rw [show 265 = 86 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (265 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_265 :
    recurrence4B3A4.coeff 265 =
      (((15424940187931269570493148935719224 * 10 ^ 70 +
        7379770984457804172057204691300814793807023580130468751065349464167947) * 10 ^ 70 +
        3429323281786150415048029888688911247946511089064967866001404998428264) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (265 - x)) = _
  rw [show 266 = 87 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (266 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_266 :
    recurrence4B3A4.coeff 266 =
      -(((2103840496021547360452116371668644 * 10 ^ 70 +
        1057327211486152236085025969375759643359543816902376770563246235649731) * 10 ^ 70 +
        8021273654417470344337066103227693575643322759711199552589590546571240) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (266 - x)) = _
  rw [show 267 = 88 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (267 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_267 :
    recurrence4B3A4.coeff 267 =
      -(((383806252021653240785649741784834 * 10 ^ 70 +
        1528287219062692705721588826502035325897795661459084867556340396052271) * 10 ^ 70 +
        9056578332981300539116347732984832629769914176044407666587905872714530) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (267 - x)) = _
  rw [show 268 = 89 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (268 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_268 :
    recurrence4B3A4.coeff 268 =
      (((501793254296427666428158972305162 * 10 ^ 70 +
        1071998540818671232215800122674950614890961711889433091630380096900368) * 10 ^ 70 +
        9889165604223577240316212886558658804464425918537178565640597631012421) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (268 - x)) = _
  rw [show 269 = 90 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 11 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (269 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_269 :
    recurrence4B3A4.coeff 269 =
      -(((293380975201200755931500049435971 * 10 ^ 70 +
        8340813341170181176739172272801170821924522740103384066727515269661633) * 10 ^ 70 +
        1492609126148510109584087790394799549028956473742112475244137461055125) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (269 - x)) = _
  rw [show 270 = 91 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 10 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (270 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_270 :
    recurrence4B3A4.coeff 270 =
      (((139476580418114380304825639317171 * 10 ^ 70 +
        4839724450135537051747889901486153243294262132101800926067238523176566) * 10 ^ 70 +
        5120862048595348215002232248897975389382980915228777527293622877458357) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (270 - x)) = _
  rw [show 271 = 92 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 9 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (271 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_271 :
    recurrence4B3A4.coeff 271 =
      -(((59836251681198190225644740211663 * 10 ^ 70 +
        7681805167409891175905018333448214594343850739185216696832893201199467) * 10 ^ 70 +
        7796965506151888632123474020915754732682740874640658748950487693084500) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (271 - x)) = _
  rw [show 272 = 93 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 8 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (272 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_272 :
    recurrence4B3A4.coeff 272 =
      (((23993838635711418307492964263542 * 10 ^ 70 +
        5541224860847948133917047981176426607728335617253775815413455227763433) * 10 ^ 70 +
        7079738545347724718965384234610382087686367094636839056741622871814029) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (272 - x)) = _
  rw [show 273 = 94 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 7 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (273 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_273 :
    recurrence4B3A4.coeff 273 =
      -(((9120690554770471950143129573268 * 10 ^ 70 +
        9396158766066987264469991347077094195132244452941571139092056090035978) * 10 ^ 70 +
        6459205885439143178359185743940134206765040440241313514048142831329551) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (273 - x)) = _
  rw [show 274 = 95 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 6 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (274 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_274 :
    recurrence4B3A4.coeff 274 =
      (((3304252153105216594761395240844 * 10 ^ 70 +
        5294511565361741471486484286035853107156330450328890559599089036328611) * 10 ^ 70 +
        5929889112622867807714850875522489876272582880161732552625931265438964) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (274 - x)) = _
  rw [show 275 = 96 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 5 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (275 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_275 :
    recurrence4B3A4.coeff 275 =
      -(((1141731304012086984538121464326 * 10 ^ 70 +
        6018490902169508556497014548264331674202284562708892820172010712972553) * 10 ^ 70 +
        6533391581151712276972144253061407770467736554729542540344574512367840) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (275 - x)) = _
  rw [show 276 = 97 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 4 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (276 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_276 :
    recurrence4B3A4.coeff 276 =
      (((375320799065876464994202718374 * 10 ^ 70 +
        3675176555155657022481823197875260641386957455488864223329016950871687) * 10 ^ 70 +
        4367098002708167757178410449574187693992150569825624377449574671268937) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (276 - x)) = _
  rw [show 277 = 98 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 3 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (277 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_277 :
    recurrence4B3A4.coeff 277 =
      -(((116696621427647539591637102147 * 10 ^ 70 +
        3403877628448696364942074983612516821849991891275426978949585007656333) * 10 ^ 70 +
        8807457583333221588510785527122135757941545207960670311007326475170336) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (277 - x)) = _
  rw [show 278 = 99 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 2 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (278 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_278 :
    recurrence4B3A4.coeff 278 =
      (((33968463048415396149568699211 * 10 ^ 70 +
        6805212208157679553864459443061787124892085343187696324907159360164309) * 10 ^ 70 +
        5190338785772295223900374606729278043997433641584669701877941450495729) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (278 - x)) = _
  rw [show 279 = 100 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 1 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (279 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_279 :
    recurrence4B3A4.coeff 279 =
      -(((9093408220487146119642826777 * 10 ^ 70 +
        7289467238086582100635276646693746484378874990448757894976548033300126) * 10 ^ 70 +
        3834446300332880325369491299268604522376944937422495616945865426597797) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (279 - x)) = _
  rw [show 280 = 101 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (280 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_280 :
    recurrence4B3A4.coeff 280 =
      (((2163707894380213283710952244 * 10 ^ 70 +
        1527762352809112394705789968887923254235083858113419506607844293823716) * 10 ^ 70 +
        2441582158565662182813832535242597860427978557914261554877679554099723) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (280 - x)) = _
  rw [show 281 = 102 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 31 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (281 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_281 :
    recurrence4B3A4.coeff 281 =
      -(((421564980604112687946980695 * 10 ^ 70 +
        4818103806083590786131879629940474239158595390158569596494747924848104) * 10 ^ 70 +
        0407812808339023925080941538669234654428820681538425921539066689154756) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (281 - x)) = _
  rw [show 282 = 103 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 30 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (282 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_282 :
    recurrence4B3A4.coeff 282 =
      (((48088503355252562944210000 * 10 ^ 70 +
        1628063081117426270332359942735376377283581828634848954309130442231467) * 10 ^ 70 +
        5124043495047022711075481017284980334120677871727351452750782834791348) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (282 - x)) = _
  rw [show 283 = 104 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 29 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (283 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_283 :
    recurrence4B3A4.coeff 283 =
      (((9140111395711809664422684 * 10 ^ 70 +
        0291132443670204696249178457604609188719456867045701131046812597404952) * 10 ^ 70 +
        4434230337176717893885073714141644130105519514228539110830262761725311) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (283 - x)) = _
  rw [show 284 = 105 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 28 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (284 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_284 :
    recurrence4B3A4.coeff 284 =
      -(((8884643199562520030909140 * 10 ^ 70 +
        4458093954789086991662754579918525235352247116016669507087945321720265) * 10 ^ 70 +
        5410633488087342476314979163487327272400837711192649700136732106320199) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (284 - x)) = _
  rw [show 285 = 106 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 27 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (285 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_285 :
    recurrence4B3A4.coeff 285 =
      (((3998244856203530177734377 * 10 ^ 70 +
        2901779083577325904997961231115526220232645432280001599563814331612483) * 10 ^ 70 +
        2631069328038218929020752679901929295698285153024331613875668422374971) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (285 - x)) = _
  rw [show 286 = 107 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (286 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_286 :
    recurrence4B3A4.coeff 286 =
      -(((1408470253630098014148235 * 10 ^ 70 +
        8750994557069238472102636779927189773465442266143653454236131953761457) * 10 ^ 70 +
        3196073471400987722488269425660002685157166495498035310746096722750199) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (286 - x)) = _
  rw [show 287 = 108 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 25 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (287 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_287 :
    recurrence4B3A4.coeff 287 =
      (((428258357625952747276528 * 10 ^ 70 +
        3764536486621471239690418852411178316626489813909612582524454914494707) * 10 ^ 70 +
        9529528380789846029263039630535892458300873079025685985755037218572169) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (287 - x)) = _
  rw [show 288 = 109 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 24 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (288 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_288 :
    recurrence4B3A4.coeff 288 =
      -(((116300705409498534090563 * 10 ^ 70 +
        7085017125314787704037190246232054842953387693080178126110234001043624) * 10 ^ 70 +
        7583502596225993163521785529669579172023275389184983132313992246677838) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (288 - x)) = _
  rw [show 289 = 110 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 23 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (289 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_289 :
    recurrence4B3A4.coeff 289 =
      (((28608156234871493318699 * 10 ^ 70 +
        0767261803498819149191702948487076573720422311498398187747781159088678) * 10 ^ 70 +
        5517071887149606453793176500575581180899283186405960539730600814270837) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (289 - x)) = _
  rw [show 290 = 111 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (290 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_290 :
    recurrence4B3A4.coeff 290 =
      -(((6405928967319743493014 * 10 ^ 70 +
        9287429287681280378986115840995624324556423002324258233783163060108979) * 10 ^ 70 +
        5687212145244017320799619553242290803566504243503479133874580432320305) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (290 - x)) = _
  rw [show 291 = 112 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 21 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (291 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_291 :
    recurrence4B3A4.coeff 291 =
      (((1304769057131996391366 * 10 ^ 70 +
        9966626878345372983144566767055586372521023202318514551131537685831309) * 10 ^ 70 +
        3399177275192390878702706736914750236580799303706443131805816770910579) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (291 - x)) = _
  rw [show 292 = 113 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 20 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (292 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_292 :
    recurrence4B3A4.coeff 292 =
      -(((240311059019094910324 * 10 ^ 70 +
        5637193310146192990527192742067629599238637895170858395655573402558269) * 10 ^ 70 +
        4152220506676112373588314112643363780117410288128733571410014866532188) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (292 - x)) = _
  rw [show 293 = 114 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 19 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (293 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_293 :
    recurrence4B3A4.coeff 293 =
      (((39514974651687684243 * 10 ^ 70 +
        5055931627983742862510829461986283546187502740474478855164027269827214) * 10 ^ 70 +
        6808146605927720021860480869011170394610161049043816523305066896108541) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (293 - x)) = _
  rw [show 294 = 115 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 18 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (294 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_294 :
    recurrence4B3A4.coeff 294 =
      -(((5656043345917011716 * 10 ^ 70 +
        4263233150444812469698093087210369611392784541139234764801305478855849) * 10 ^ 70 +
        4974687592143273275483310703265178229481380917933497910175487462565850) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (294 - x)) = _
  rw [show 295 = 116 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 17 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (295 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_295 :
    recurrence4B3A4.coeff 295 =
      (((665991139298971372 * 10 ^ 70 +
        4028732943427898077403169124972652634923365194990569106944635505819364) * 10 ^ 70 +
        7366239289945378505106352334199686169220368146973592685700672521682820) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (295 - x)) = _
  rw [show 296 = 117 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (296 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_296 :
    recurrence4B3A4.coeff 296 =
      -(((54004257330386423 * 10 ^ 70 +
        9347161551734269697817635729433488182215672404028276465329488543425364) * 10 ^ 70 +
        4606980784716576880152620129347182619655422909961490586091213129914144) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (296 - x)) = _
  rw [show 297 = 118 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 15 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (297 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_297 :
    recurrence4B3A4.coeff 297 =
      -(((136741486262853 * 10 ^ 70 +
        8977674482003145914067677581955925543184580900139780890858734574649348) * 10 ^ 70 +
        2174500561798989095053483454282159856355081472862544334978881269709966) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (297 - x)) = _
  rw [show 298 = 119 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 14 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (298 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_298 :
    recurrence4B3A4.coeff 298 =
      (((1150270989904106 * 10 ^ 70 +
        2639333639774956232884781052654498638167311202894650661263628201421055) * 10 ^ 70 +
        7948943221452131649268381303302163917074865668466224777884525627413603) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (298 - x)) = _
  rw [show 299 = 120 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 13 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (299 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_299 :
    recurrence4B3A4.coeff 299 =
      -(((282958144507157 * 10 ^ 70 +
        6337877177643649318687505603214746838100564500428554788481778631930057) * 10 ^ 70 +
        5366524324840866153976942937177357717441959000352873148680858564542475) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (299 - x)) = _
  rw [show 300 = 121 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (300 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_300 :
    recurrence4B3A4.coeff 300 =
      (((46851271696355 * 10 ^ 70 +
        2234107504002222160203680985299917728380589828476132290763488607594489) * 10 ^ 70 +
        0411274080241452282192801053865519979341625670377547651124400798993626) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (300 - x)) = _
  rw [show 301 = 122 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 11 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (301 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_301 :
    recurrence4B3A4.coeff 301 =
      -(((6041594485685 * 10 ^ 70 +
        4566960915032505885963592651487222815554816222539196399533294823046758) * 10 ^ 70 +
        8986769549742720522647458451571302739762034232523131451510955442122173) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (301 - x)) = _
  rw [show 302 = 123 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 10 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (302 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_302 :
    recurrence4B3A4.coeff 302 =
      (((617741522438 * 10 ^ 70 +
        0136439189067470112960599556882630156241161668469445222292958240671190) * 10 ^ 70 +
        5263281108457988407162016058686180801916500155884632676398193571863208) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (302 - x)) = _
  rw [show 303 = 124 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 9 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (303 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_303 :
    recurrence4B3A4.coeff 303 =
      -(((47636885250 * 10 ^ 70 +
        8494320125946318296252682781641259487002085748207708574509601716485691) * 10 ^ 70 +
        7550653743917625228143092369118778526694988208408019174060367135254475) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (303 - x)) = _
  rw [show 304 = 125 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 8 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (304 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_304 :
    recurrence4B3A4.coeff 304 =
      (((2199903365 * 10 ^ 70 +
        4367290094223103665978767515080241220364208772059997498924448466032280) * 10 ^ 70 +
        0293184875076534377734037113475852954989929112585428284385243609489486) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (304 - x)) = _
  rw [show 305 = 126 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 7 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (305 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_305 :
    recurrence4B3A4.coeff 305 =
      (((47863889 * 10 ^ 70 +
        4824934730033792587195132824854490800343957221760044351916063381050841) * 10 ^ 70 +
        6703307812463601149119213835113167498846437395052147241124323403295939) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (305 - x)) = _
  rw [show 306 = 127 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 6 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B3A4_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (306 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_306 :
    recurrence4B3A4.coeff 306 =
      -(((21775099 * 10 ^ 70 +
        2171295828534502549854335464459098343868065747407378191957339101618271) * 10 ^ 70 +
        5156813472536362597007323732806375454419683790367382484396637869092905) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (306 - x)) = _
  rw [show 307 = 128 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 5 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
