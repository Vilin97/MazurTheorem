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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
