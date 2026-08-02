/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B2A4 coefficient convolution

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

private theorem recurrence4B2A4_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (216 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_216 :
    recurrence4B2A4.coeff 216 =
      -(((63762994325171324934031074669622217433832829585118447881 * 10 ^ 70 +
        1198825374972891139972808578273562253776471072438123000896862451525340) * 10 ^ 70 +
        2098955694890801747927878536393824525663089908290179057437363324536159) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (216 - x)) = _
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
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (217 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_217 :
    recurrence4B2A4.coeff 217 =
      (((41502983888800793785550937926167715717379405223032860458 * 10 ^ 70 +
        8467241192931725889510030297106515620055008177526646455338243552762411) * 10 ^ 70 +
        0867241935540039163327899575438770833055558736794510513633354871690618) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (217 - x)) = _
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
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (218 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_218 :
    recurrence4B2A4.coeff 218 =
      -(((25244755845665170679788638357588337786960783102689842832 * 10 ^ 70 +
        5911207050510025927839034129482920201069197897233236799153200149838344) * 10 ^ 70 +
        3677123890118641656015394765896434325355823030350658614877934872506738) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (218 - x)) = _
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
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (219 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_219 :
    recurrence4B2A4.coeff 219 =
      (((14604048688918919862442960216978605667154659403179996377 * 10 ^ 70 +
        9592366365161223798262914048488385373568659324905680807578359826316189) * 10 ^ 70 +
        5071547162571778749820421510600136418696365344692455740723360503508960) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (219 - x)) = _
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
  rw [recurrence4B2A4_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (220 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_220 :
    recurrence4B2A4.coeff 220 =
      -(((8114332685945279051295836488413571033723562475324235413 * 10 ^ 70 +
        4516897138284916469903134752344636426689742089603370073175777051041117) * 10 ^ 70 +
        9109270809896767230660392409540033578453486845937743297639760857351881) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (220 - x)) = _
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
    rw [show 83 = 31 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (221 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_221 :
    recurrence4B2A4.coeff 221 =
      (((4356238388947067762607737343286114040207570121712298280 * 10 ^ 70 +
        1108453324433974244222238463369514958325560978684741401528798805390553) * 10 ^ 70 +
        1101497502130142801203380320620556539307004722419455856297717637739382) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (221 - x)) = _
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
    rw [show 83 = 30 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (222 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_222 :
    recurrence4B2A4.coeff 222 =
      -(((2268436445978979565702508866530724519919819535981893456 * 10 ^ 70 +
        2899051578997106424432564456075135576723085834678255739352866470923875) * 10 ^ 70 +
        8620099083539917191273098644727683305060892138029485468599788959275866) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (222 - x)) = _
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
    rw [show 83 = 29 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (223 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_223 :
    recurrence4B2A4.coeff 223 =
      (((1148725437671083307182298041486054707894679999503534237 * 10 ^ 70 +
        1100191967825872200171306306791837645999324508789595695544462173402920) * 10 ^ 70 +
        0425251903105670447634334647353405419759322078649021292070642986900359) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (223 - x)) = _
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
    rw [show 83 = 28 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (224 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_224 :
    recurrence4B2A4.coeff 224 =
      -(((566682660770767732908032150644126605262178776317762135 * 10 ^ 70 +
        2996285590277200240952446096869566815934428249478202236087005467309807) * 10 ^ 70 +
        5405697947318428226744469965222535566854234279757948109175537609143524) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (224 - x)) = _
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
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (225 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_225 :
    recurrence4B2A4.coeff 225 =
      (((272655583389565998237908376288739273846979690041888911 * 10 ^ 70 +
        9489054227748486214535340859561449491875172924896584687676908429177744) * 10 ^ 70 +
        9496052800209450450336843753526172784552275171488993865087017636912787) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (225 - x)) = _
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
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (226 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_226 :
    recurrence4B2A4.coeff 226 =
      -(((128051724423123565304599882346885955973503139442340444 * 10 ^ 70 +
        6065467395405393909717268548315346783206178821198127145303130668354174) * 10 ^ 70 +
        0515138044564526535587721097305035048315925834140654495943804448070636) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (226 - x)) = _
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
    rw [show 83 = 25 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (227 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_227 :
    recurrence4B2A4.coeff 227 =
      (((58731860779261278546196149926183256201799810734694468 * 10 ^ 70 +
        2867462022502225333513621608411229446899513681133119129987188032136452) * 10 ^ 70 +
        3133941186277582841600933760772786471410920971422310826021053597210218) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (227 - x)) = _
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
    rw [show 83 = 24 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (228 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_228 :
    recurrence4B2A4.coeff 228 =
      -(((26315080401405971966268443191972019878024094633583842 * 10 ^ 70 +
        5654584820129625061582678299024290743847913790741464185882199466064471) * 10 ^ 70 +
        4163757348803949726846237285181352010995459236583591834099913328357087) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (228 - x)) = _
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
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (229 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_229 :
    recurrence4B2A4.coeff 229 =
      (((11519310247239823018855771862297490421817210116786883 * 10 ^ 70 +
        1331837122137828217797209701582953660322834805619590463682867378566118) * 10 ^ 70 +
        6975303444412324627564564387909511748610933161147044024459384052082377) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (229 - x)) = _
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
    rw [show 83 = 22 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (230 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_230 :
    recurrence4B2A4.coeff 230 =
      -(((4926283233120750599811424750910743310516314690545951 * 10 ^ 70 +
        8369185581899224047066805209874816968262288481512816070467085873777288) * 10 ^ 70 +
        8092161080309035187360010844845427758931820393058005752603839463533269) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (230 - x)) = _
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
    rw [show 83 = 21 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (231 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_231 :
    recurrence4B2A4.coeff 231 =
      (((2057765943308283759127424238380402311042130005241214 * 10 ^ 70 +
        7182536535576680352437808057795664870795532906534708173726888673561420) * 10 ^ 70 +
        7000069736290190009283660943457742499585397153264207379958254233835954) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (231 - x)) = _
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
    rw [show 83 = 20 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (232 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_232 :
    recurrence4B2A4.coeff 232 =
      -(((839248380293127983492071442472265304738383403122184 * 10 ^ 70 +
        3721151773763770175118892702963029277120101721480569424960402104192960) * 10 ^ 70 +
        7559709914256974690638847330083355747090089151825220686274362419573397) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (232 - x)) = _
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
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (233 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_233 :
    recurrence4B2A4.coeff 233 =
      (((333989651859483297313378539891321782390546932616894 * 10 ^ 70 +
        3749235821834786154187970760826651518661927690501516498322906933747721) * 10 ^ 70 +
        6135366756725766880222280470063274911057940383251612503608901626670030) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (233 - x)) = _
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
    rw [show 83 = 18 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (234 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_234 :
    recurrence4B2A4.coeff 234 =
      -(((129568414711151860000558692580389034405862927624410 * 10 ^ 70 +
        3473726134307399381428943034819860364395271710786297216662078724935146) * 10 ^ 70 +
        0338307956456897318806039839036792069589610743500205050332047107368109) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (234 - x)) = _
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
    rw [show 83 = 17 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (235 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_235 :
    recurrence4B2A4.coeff 235 =
      (((48923638852370445834367613592320821073534566234763 * 10 ^ 70 +
        4440081947954070042984744207063471774894756091204029762227893553802376) * 10 ^ 70 +
        5469773945847757798690265550867441716751016773333294466461270928835075) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (235 - x)) = _
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
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (236 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_236 :
    recurrence4B2A4.coeff 236 =
      -(((17935324950747581978607408956199163300464698855783 * 10 ^ 70 +
        1498914524525570977631221981064583124720275827791631768529667975136018) * 10 ^ 70 +
        0923398416024730515749338488398532441754339757258072538219169590751207) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (236 - x)) = _
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
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (237 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_237 :
    recurrence4B2A4.coeff 237 =
      (((6357156376068822616035225927468202505892584925590 * 10 ^ 70 +
        5380265572536089303343053895200898866126761954466468957649532794944074) * 10 ^ 70 +
        2452096188468980655391832222438235343142939829295025462235631771162871) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (237 - x)) = _
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
    rw [show 83 = 14 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (238 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_238 :
    recurrence4B2A4.coeff 238 =
      -(((2162831334483442405197190139220742659866581531971 * 10 ^ 70 +
        7711284217100458581689661956243548459605873846385341330959495548923203) * 10 ^ 70 +
        5749183858626830922909400285639008477543444661885025283712026736106132) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (238 - x)) = _
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
    rw [show 83 = 13 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (239 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_239 :
    recurrence4B2A4.coeff 239 =
      (((696795581315735572272285990082205345184861018722 * 10 ^ 70 +
        0269873432781579962976359842936625205726480836200917756956896114852330) * 10 ^ 70 +
        5397201058134585012028916743731872333284975383368875793930433705134277) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (239 - x)) = _
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
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (240 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_240 :
    recurrence4B2A4.coeff 240 =
      -(((206699569848651844214125769068088128845801699407 * 10 ^ 70 +
        9477964266710408903215582779374846990714199578335837387965793690547193) * 10 ^ 70 +
        1652700452874567984646285205102057945414693959563415639176696364016113) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (240 - x)) = _
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
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (241 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_241 :
    recurrence4B2A4.coeff 241 =
      (((52629823648634770259093320626600465661492215157 * 10 ^ 70 +
        0695688573508184089614289463941682670115593208511690551416660458667439) * 10 ^ 70 +
        3759585111427525809826302820501372767307438543258850478432226389910105) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (241 - x)) = _
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
    rw [show 83 = 10 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (242 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_242 :
    recurrence4B2A4.coeff 242 =
      -(((8740036669557649246143787883754867830340329987 * 10 ^ 70 +
        6723307409795232348544457832679663908637686951238138358321094725073780) * 10 ^ 70 +
        3967917430165057055063691531357120917236886639735916381616197177960936) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (242 - x)) = _
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
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (243 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_243 :
    recurrence4B2A4.coeff 243 =
      -(((1477421557232034532221114076237048019636826293 * 10 ^ 70 +
        6902440679959315185393823792946050760535300020088779666969650521192319) * 10 ^ 70 +
        3624310336646687269422423008484920612276194670169684307336024866329427) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (243 - x)) = _
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
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (244 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_244 :
    recurrence4B2A4.coeff 244 =
      (((2573954026781070862627660590849037759351125260 * 10 ^ 70 +
        9073948170606756648049974924578320582063744068337401355798981951330668) * 10 ^ 70 +
        7514854605656771737652942775665639450385989942009186840931447984523805) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (244 - x)) = _
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
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (245 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_245 :
    recurrence4B2A4.coeff 245 =
      -(((1808234428681322094624850059881093883117494770 * 10 ^ 70 +
        6977233791209834095070691085838637651246817766084834871998621606235046) * 10 ^ 70 +
        1246000128257656938635477742871657654613199437484146662420787636681977) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (245 - x)) = _
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
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (246 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_246 :
    recurrence4B2A4.coeff 246 =
      (((1022636300822137409318573662489725618761610064 * 10 ^ 70 +
        4983809373632550546348979380417819516091513025098443861856418289698787) * 10 ^ 70 +
        9349230086244777498040140977422650692158022824033930674704948010224215) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (246 - x)) = _
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
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (247 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_247 :
    recurrence4B2A4.coeff 247 =
      -(((520590591650682011788549336345715065318374020 * 10 ^ 70 +
        0932437153474331064338905710236923984156330347803198138692057544980775) * 10 ^ 70 +
        3395086018251390178499572914410100231078201890431945797219192125574039) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (247 - x)) = _
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
    rhs
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (248 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_248 :
    recurrence4B2A4.coeff 248 =
      (((247884709027763749552822530119983402540236766 * 10 ^ 70 +
        3214251855898288864718228756903298117940364998727921588028723600960144) * 10 ^ 70 +
        0566923716846565065669777982258115277249908754264825251497046044588488) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (248 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (249 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_249 :
    recurrence4B2A4.coeff 249 =
      -(((112252098445660785857174333623376269471426503 * 10 ^ 70 +
        6144885975284816647091985662061337388952954028285085988718928512443041) * 10 ^ 70 +
        7260162531958260750749595518390265999494049470140810670204994978303263) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (249 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (250 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_250 :
    recurrence4B2A4.coeff 250 =
      (((48717338058998127084421328502049622121654789 * 10 ^ 70 +
        6345710101253439111586479196199128342611004008400089842126554493625606) * 10 ^ 70 +
        2522026653916509184588961382037672732625965632574738732297170239850986) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (250 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (251 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_251 :
    recurrence4B2A4.coeff 251 =
      -(((20331783392667689324414413107743024703033017 * 10 ^ 70 +
        5392168289974746717131332802646744972888774808624236014712715398236928) * 10 ^ 70 +
        3685934898833216155990438989945825082543361825847723109084790460041504) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (251 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (252 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_252 :
    recurrence4B2A4.coeff 252 =
      (((8166920074885272137192707277612534405133700 * 10 ^ 70 +
        9768108434185049589976683825094756190875797195983313189085072986241205) * 10 ^ 70 +
        9529668864002702862192605677778963506222298206602044995407868488344173) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (252 - x)) = _
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
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (253 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_253 :
    recurrence4B2A4.coeff 253 =
      -(((3155131110350471156517864434452338826315315 * 10 ^ 70 +
        3301253855302085345805437604205296229726583737312743245054573405406802) * 10 ^ 70 +
        1742207207218258216333787847400287414784965130311038585758591796193265) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (253 - x)) = _
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
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (254 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_254 :
    recurrence4B2A4.coeff 254 =
      (((1169975868935888988211850063555807890423003 * 10 ^ 70 +
        0199783997294183622075644929038070186945882876447063367125493049995388) * 10 ^ 70 +
        1777057162215959961013632834875795065455243916285994673050913548458990) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (254 - x)) = _
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
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (255 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_255 :
    recurrence4B2A4.coeff 255 =
      -(((415042752812289781086058489435137072806275 * 10 ^ 70 +
        9429563176392617414040568189016109813069810096833277864734066312184724) * 10 ^ 70 +
        1392389958166063989320144805241457075196584312761731186506659051434230) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (255 - x)) = _
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
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (256 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_256 :
    recurrence4B2A4.coeff 256 =
      (((140152562309146105263806519398432155098669 * 10 ^ 70 +
        8402131537624330324629895156161063031227666461947652034057399166928934) * 10 ^ 70 +
        7837527683465360467535315023928804103039510192122542711294224918697227) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (256 - x)) = _
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
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (257 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_257 :
    recurrence4B2A4.coeff 257 =
      -(((44714358550152538840981032070835779135088 * 10 ^ 70 +
        3091012665889998700866809190781519622878939056646181876959740733840426) * 10 ^ 70 +
        1898781903760044983657470000657401513310333752641660858962105880650783) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (257 - x)) = _
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
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (258 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_258 :
    recurrence4B2A4.coeff 258 =
      (((13318978432944377299039994468663903214729 * 10 ^ 70 +
        0783739195005546510240971628319928677963100986672501809188393146318808) * 10 ^ 70 +
        9414294183022395252736632224591259887214610781889882243101700435530223) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (258 - x)) = _
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
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (259 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_259 :
    recurrence4B2A4.coeff 259 =
      -(((3627939608531022452148827983692843740122 * 10 ^ 70 +
        4595377663141181159707277861995795086375417007255544395127323243398346) * 10 ^ 70 +
        6100737436932501207814951634254820564288983502790462290805321254224442) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (259 - x)) = _
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
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (260 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_260 :
    recurrence4B2A4.coeff 260 =
      (((866061667704277467368178799699627628307 * 10 ^ 70 +
        2160461800103124839604358831714263728417413620108300933161563742659408) * 10 ^ 70 +
        4304425235627822912642103332723952611461825920901554682496717112063089) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (260 - x)) = _
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
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (261 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_261 :
    recurrence4B2A4.coeff 261 =
      -(((161286158111695095123304651776059594501 * 10 ^ 70 +
        1784326692380633174501287899732501728303466052373994810688944832970098) * 10 ^ 70 +
        2240369494894603845306351615066732249053749858443281160476430277537836) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (261 - x)) = _
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
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (262 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_262 :
    recurrence4B2A4.coeff 262 =
      (((11488212318236743515296274763572907778 * 10 ^ 70 +
        2988632518601307619330915605374971256403379970938627459130102945065363) * 10 ^ 70 +
        8557016028582277624442802547323661817614578568507301077794407291811834) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (262 - x)) = _
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
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (263 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_263 :
    recurrence4B2A4.coeff 263 =
      (((8706959373614717314802233169881832840 * 10 ^ 70 +
        9611229569968006458216972269329843722898805898661496226981752948783384) * 10 ^ 70 +
        7815416180251739436308589415838444629098454163398026740132465086620855) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (263 - x)) = _
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
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (264 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_264 :
    recurrence4B2A4.coeff 264 =
      -(((6172928788036532122476328645518304449 * 10 ^ 70 +
        6508219907444786034868302924400433138817766746996129336605453424291613) * 10 ^ 70 +
        4962150889717862319773152809893961026092073905991388537874255397123284) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (264 - x)) = _
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
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (265 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_265 :
    recurrence4B2A4.coeff 265 =
      (((2779478096919087517561491480239297524 * 10 ^ 70 +
        8833963038844710144339124030443317729571956348740483675946504858166586) * 10 ^ 70 +
        0100829379055882576976098998390285513599878239037904869110531022965303) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (265 - x)) = _
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
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (266 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_266 :
    recurrence4B2A4.coeff 266 =
      -(((1048929080843772534055147414807387858 * 10 ^ 70 +
        5900703097715895560529754141380601550126844612139372160939648911530170) * 10 ^ 70 +
        4365157584433972108194514181774392026826781905968625838775070301500223) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (266 - x)) = _
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
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (267 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_267 :
    recurrence4B2A4.coeff 267 =
      (((361022768514372942967373218452714641 * 10 ^ 70 +
        6742213481698359748935738165912837733152270271913979737240986055541437) * 10 ^ 70 +
        0896587070272657469377957700830579857016645677239710624888949006031206) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (267 - x)) = _
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
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (268 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_268 :
    recurrence4B2A4.coeff 268 =
      -(((119611217923065334287878663464936777 * 10 ^ 70 +
        2764663428124341479305707706926587469500854804922784562321761559204548) * 10 ^ 70 +
        6259483053661580489361024734383621092187086319725962128507351063233669) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (268 - x)) = _
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
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (269 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_269 :
    recurrence4B2A4.coeff 269 =
      (((40096233818016085309299606384676015 * 10 ^ 70 +
        2297362028309761759587201722048929625082843378722877250622672549628971) * 10 ^ 70 +
        0517967484174023682932172657775263502077798917589565953145520997416153) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (269 - x)) = _
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
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (270 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_270 :
    recurrence4B2A4.coeff 270 =
      -(((14167810490793897420424205187566176 * 10 ^ 70 +
        8709827763912880933336434281003327110775932650111325262113440978293161) * 10 ^ 70 +
        1269525091897442643009283532004765139208936906602885874214109775494953) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (270 - x)) = _
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
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (271 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_271 :
    recurrence4B2A4.coeff 271 =
      (((5351135931574662746061280362766716 * 10 ^ 70 +
        9493210813000900788386252203295430960525901062953105273314533243258794) * 10 ^ 70 +
        5691676577880413565054360316770716165697529337725665440913696366843272) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (271 - x)) = _
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
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (272 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_272 :
    recurrence4B2A4.coeff 272 =
      -(((2122348227363119441197581860752171 * 10 ^ 70 +
        6072035986904204514990015146669807984247275048789938590975400915638219) * 10 ^ 70 +
        1582235527404516293018568231772178815968388954339039155712630259167830) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (272 - x)) = _
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
    rw [show 115 = 11 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (273 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_273 :
    recurrence4B2A4.coeff 273 =
      (((856292116773396210950883083466714 * 10 ^ 70 +
        2504066838354820883504399586568688594448146681099521733203688374688789) * 10 ^ 70 +
        4617537743470343740269969076838935691829890656137781475587657689055281) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (273 - x)) = _
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
    rw [show 115 = 10 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (274 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_274 :
    recurrence4B2A4.coeff 274 =
      -(((342041182759926694927373920494022 * 10 ^ 70 +
        4951683205249891339720387078063237026661607858872650943856704480075586) * 10 ^ 70 +
        4822977214253164853590788260888665219187857861583272359544995783125309) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (274 - x)) = _
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
    rw [show 115 = 9 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (275 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_275 :
    recurrence4B2A4.coeff 275 =
      (((132981673443574913628310132674163 * 10 ^ 70 +
        6867482674880309392277874111314576568397670082091447125665257312352367) * 10 ^ 70 +
        2938362217250775789987334851715534622187042843345897282587234710565131) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (275 - x)) = _
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
    rw [show 115 = 8 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (276 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_276 :
    recurrence4B2A4.coeff 276 =
      -(((49840764978779568967390930924058 * 10 ^ 70 +
        0810515060407324049231202436954625939858467301446187894031949377176718) * 10 ^ 70 +
        1005522392667739972804238157724804279475568784263308147120625342406981) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (276 - x)) = _
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
    rw [show 115 = 7 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (277 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_277 :
    recurrence4B2A4.coeff 277 =
      (((17895263502851563503590368469691 * 10 ^ 70 +
        4107236141892483684634950739574094755187449619081849020195242166816233) * 10 ^ 70 +
        7080786296059333347496988999770307022996396922201786824327262515269645) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (277 - x)) = _
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
    rw [show 115 = 6 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (278 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_278 :
    recurrence4B2A4.coeff 278 =
      -(((6119163007893538555947812174575 * 10 ^ 70 +
        6620307414408691161024575253402574982230146629192735590526650040654982) * 10 ^ 70 +
        7686427043987843255027039347731910094566386705846184216555435271015727) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (278 - x)) = _
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
    rw [show 115 = 5 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (279 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_279 :
    recurrence4B2A4.coeff 279 =
      (((1977819197030521113939928910923 * 10 ^ 70 +
        6180488525223890270049624099456813632110815090416572748230859117385100) * 10 ^ 70 +
        2266413003429704977959586767081063418067319584804412335207833624199227) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (279 - x)) = _
  rw [show 280 = 101 +
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
  rw [recurrence4B2A4_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (280 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_280 :
    recurrence4B2A4.coeff 280 =
      -(((597710087861672253939152566001 * 10 ^ 70 +
        2197122061063567169393380762255555991524126897561501784186620427794597) * 10 ^ 70 +
        7388882536720210024252847061045017699507859699861109940071608136900462) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (280 - x)) = _
  rw [show 281 = 102 +
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
  rw [recurrence4B2A4_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (281 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_281 :
    recurrence4B2A4.coeff 281 =
      (((166001841842094956996534480613 * 10 ^ 70 +
        2274474153146152486712595199327278568338878371796678246616709571802825) * 10 ^ 70 +
        7318873289334185706435222299174580516936668295888385042830656552494488) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (281 - x)) = _
  rw [show 282 = 103 +
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
  rw [recurrence4B2A4_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (282 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_282 :
    recurrence4B2A4.coeff 282 =
      -(((41069538245658022709410643154 * 10 ^ 70 +
        0850673477731790083080659625585991494456278464015077727166130714450594) * 10 ^ 70 +
        1619181049473708710425391754789575413319316511632814450494092999359151) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (282 - x)) = _
  rw [show 283 = 104 +
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
  rw [recurrence4B2A4_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (283 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_283 :
    recurrence4B2A4.coeff 283 =
      (((8432613365932767513106312800 * 10 ^ 70 +
        1994697612452804045380129709063298165350921845589238440111525559986453) * 10 ^ 70 +
        2221136471184089074081141327561604821141857246826649298888377596136346) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (283 - x)) = _
  rw [show 284 = 105 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (284 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_284 :
    recurrence4B2A4.coeff 284 =
      -(((1111660795608050353613930905 * 10 ^ 70 +
        1652658570591181184369357911743065196465053188745181603801429214732521) * 10 ^ 70 +
        0225027593871477604359591760654856755431989711599025057416479510430947) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (284 - x)) = _
  rw [show 285 = 106 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 31 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (285 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_285 :
    recurrence4B2A4.coeff 285 =
      -(((109535104403255444193538560 * 10 ^ 70 +
        3066418591635153592237989900705121525065531896936780112196666042573668) * 10 ^ 70 +
        9625830102648819289777793526636479303907987376192520840945931290564356) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (285 - x)) = _
  rw [show 286 = 107 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 30 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (286 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_286 :
    recurrence4B2A4.coeff 286 =
      (((151727232633205517020836761 * 10 ^ 70 +
        1778613894082890417857312488627972309657167201835576322183873725423243) * 10 ^ 70 +
        5012458822367279463251046422994328701571374216992268240460088275178428) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (286 - x)) = _
  rw [show 287 = 108 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 29 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (287 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_287 :
    recurrence4B2A4.coeff 287 =
      -(((72001580661553729723264021 * 10 ^ 70 +
        6046437145264973829584507755345327574375604937275535583102552622979915) * 10 ^ 70 +
        2495683532124488515275750444816070185500417193361718148082447536811815) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (287 - x)) = _
  rw [show 288 = 109 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 28 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (288 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_288 :
    recurrence4B2A4.coeff 288 =
      (((25916966337025013303459252 * 10 ^ 70 +
        5134644533164500716674599340782072128812017905516054869394700642629532) * 10 ^ 70 +
        7233563117596361227968538927767232639982698630674349439583890733957501) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (288 - x)) = _
  rw [show 289 = 110 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 27 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (289 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_289 :
    recurrence4B2A4.coeff 289 =
      -(((7955689825198669725878092 * 10 ^ 70 +
        7269871759943304643246355806809217100028759376786430878903249707698819) * 10 ^ 70 +
        4456812668708928194283869792860459539250556042714694657376736256930070) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (289 - x)) = _
  rw [show 290 = 111 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (290 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_290 :
    recurrence4B2A4.coeff 290 =
      (((2164267495353398145022534 * 10 ^ 70 +
        9465932894208392475684608464100868894727941525786500480179406775422454) * 10 ^ 70 +
        9544534689231847126822311774374235699433244015897842015753037655388850) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (290 - x)) = _
  rw [show 291 = 112 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 25 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (291 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_291 :
    recurrence4B2A4.coeff 291 =
      -(((529469390948379761734777 * 10 ^ 70 +
        9537655464016269778501691867948052711075521474066922466075475379331677) * 10 ^ 70 +
        4155974215357293687394696671667440514632665257811412074344611303484932) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (291 - x)) = _
  rw [show 292 = 113 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 24 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (292 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_292 :
    recurrence4B2A4.coeff 292 =
      (((116900770439539526389351 * 10 ^ 70 +
        7122897551348849473254573741384129384444968357559809345472193200341596) * 10 ^ 70 +
        3396286374561535237045813113704300237305130483266665969992243665125095) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (292 - x)) = _
  rw [show 293 = 114 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 23 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (293 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_293 :
    recurrence4B2A4.coeff 293 =
      -(((23194210933135697163529 * 10 ^ 70 +
        2655341763068558022071703453438005412753589993614605377359309374082509) * 10 ^ 70 +
        7654999801745979943319782633065868933003230036747973578440664256194536) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (293 - x)) = _
  rw [show 294 = 115 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (294 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_294 :
    recurrence4B2A4.coeff 294 =
      (((4081058085983550965374 * 10 ^ 70 +
        4723361565200098674581433896051191147527991081807166457987146612680066) * 10 ^ 70 +
        6622293800964453278148097862192073979559418334406823800702209898785797) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (294 - x)) = _
  rw [show 295 = 116 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 21 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (295 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_295 :
    recurrence4B2A4.coeff 295 =
      -(((618537153695629182024 * 10 ^ 70 +
        7697823931425654802995336133984763432460133847064770322902620044885898) * 10 ^ 70 +
        6503874228054358046607396853387572419141115443696113676800067864534713) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (295 - x)) = _
  rw [show 296 = 117 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 20 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (296 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_296 :
    recurrence4B2A4.coeff 296 =
      (((75273038020124357691 * 10 ^ 70 +
        9739129796234781985882682553007662504178467405215395901283186317281732) * 10 ^ 70 +
        4746104581082236390313069337907143327116898787914725559162127650071971) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (296 - x)) = _
  rw [show 297 = 118 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 19 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (297 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_297 :
    recurrence4B2A4.coeff 297 =
      -(((5695300635668121693 * 10 ^ 70 +
        2164437430996808958979075318043214175905865377030944173850282160331442) * 10 ^ 70 +
        7091476843598818538515596470966008100613091466814792659075074950681361) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (297 - x)) = _
  rw [show 298 = 119 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 18 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (298 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_298 :
    recurrence4B2A4.coeff 298 =
      -(((297763483305709540 * 10 ^ 70 +
        8218646234961931531120640341910757240651110650826371901378612880036055) * 10 ^ 70 +
        6213601133011903180866509188207256999996741503476152063368557726040607) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (298 - x)) = _
  rw [show 299 = 120 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 17 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (299 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_299 :
    recurrence4B2A4.coeff 299 =
      (((220338644437793786 * 10 ^ 70 +
        0234810854319186366291866155050595307764458244259547774997550577789505) * 10 ^ 70 +
        2294953256170715347431820952359353951226160264048864293391539462408611) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (299 - x)) = _
  rw [show 300 = 121 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (300 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_300 :
    recurrence4B2A4.coeff 300 =
      -(((51650307588158803 * 10 ^ 70 +
        3918663274460913693104150357967389767550027087859575284078450382635346) * 10 ^ 70 +
        7490481737847919306221874337373185644304494313510952702425411965216692) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (300 - x)) = _
  rw [show 301 = 122 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 15 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (301 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_301 :
    recurrence4B2A4.coeff 301 =
      (((8438674339922750 * 10 ^ 70 +
        2630290364904141406247901376920491968191700264131280996851107726709873) * 10 ^ 70 +
        2008688527093027595535438592065510400203119055334784292705883911976857) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (301 - x)) = _
  rw [show 302 = 123 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 14 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (302 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_302 :
    recurrence4B2A4.coeff 302 =
      -(((1030619730505232 * 10 ^ 70 +
        4510757442809382763041549264570377932847411509755392982254167269824403) * 10 ^ 70 +
        1159414227965208878944948314437588959073379938364852235277466054003487) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (302 - x)) = _
  rw [show 303 = 124 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 13 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (303 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_303 :
    recurrence4B2A4.coeff 303 =
      (((85293026545254 * 10 ^ 70 +
        9154241651685360534725110954919943219928944191914063700508102039215047) * 10 ^ 70 +
        6030162249600181681180170030255399168581890523177014747018164544501421) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (303 - x)) = _
  rw [show 304 = 125 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (304 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_304 :
    recurrence4B2A4.coeff 304 =
      -(((1677164784925 * 10 ^ 70 +
        5673385474657361967506116175893985231289327103368584933510183847424147) * 10 ^ 70 +
        0854009648691998418146252842145118905251937973052132399528418779452018) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (304 - x)) = _
  rw [show 305 = 126 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 11 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (305 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_305 :
    recurrence4B2A4.coeff 305 =
      -(((921683278699 * 10 ^ 70 +
        0627717878797486511412995425768277885170698726154758447054452406059263) * 10 ^ 70 +
        3700621659779002340418457917783089368318585833281203534523836055013100) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (305 - x)) = _
  rw [show 306 = 127 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 10 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (306 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_306 :
    recurrence4B2A4.coeff 306 =
      (((200259054003 * 10 ^ 70 +
        5728549342702557780116451776566463570891940108140522935124125861395652) * 10 ^ 70 +
        8532097847364135726018637697700337697299687246148850632748879495407986) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (306 - x)) = _
  rw [show 307 = 128 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 9 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (307 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_307 :
    recurrence4B2A4.coeff 307 =
      -(((25184851815 * 10 ^ 70 +
        2131314677188985064630284568334177328375882026443802895239214342895555) * 10 ^ 70 +
        5335832297050207791934706209633174971622683556324339261172390645407802) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (307 - x)) = _
  rw [show 308 = 129 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 8 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (308 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_308 :
    recurrence4B2A4.coeff 308 =
      (((2127241998 * 10 ^ 70 +
        8344873470183831537927098341333092399297667481784624307640334907319761) * 10 ^ 70 +
        6639274826067595139250143026751811312692733633205013832876143160596256) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (308 - x)) = _
  rw [show 309 = 130 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 7 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4B2A4_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (309 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_309 :
    recurrence4B2A4.coeff 309 =
      -(((99870731 * 10 ^ 70 +
        6065541556276123292453106569354673157287751487559167142677980084908823) * 10 ^ 70 +
        6238311253747384022434219359674578635380273703781364746475393004125374) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (309 - x)) = _
  rw [show 310 = 131 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 6 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
