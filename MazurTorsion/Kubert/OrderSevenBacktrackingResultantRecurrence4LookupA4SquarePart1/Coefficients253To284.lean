/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4SquarePart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A4Square coefficient convolution

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
  recurrence4A4_coeff_44
  recurrence4A4_coeff_45
  recurrence4A4_coeff_46
  recurrence4A4_coeff_47
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

attribute [local simp]
  recurrence4A4_coeff_93
  recurrence4A4_coeff_94
  recurrence4A4_coeff_95
  recurrence4A4_coeff_96
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99

private theorem recurrence4A4Square_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (253 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_253 :
    recurrence4A4Square.coeff 253 =
      (((3334250186570544621330134459424936062695 * 10 ^ 70 +
        1365642914120568709955954841996561192315049940443501524744020493620935) * 10 ^ 70 +
        8892171425198616415680499600498661504149052057252028366445587770925068) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (253 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (254 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_254 :
    recurrence4A4Square.coeff 254 =
      -(((1307424369779126776600925686421881005534 * 10 ^ 70 +
        7231538897068108938789322819870093568795802602749443026836035311645980) * 10 ^ 70 +
        7946700394089438610074641759910412507733010966040620289015975441742460) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (254 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (255 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_255 :
    recurrence4A4Square.coeff 255 =
      (((496745582674089117666607219370469191337 * 10 ^ 70 +
        1597278715026185124692445737934678945561106670498926000664243364059104) * 10 ^ 70 +
        2706488513373146760588449396167535757164785986487327294514573279405050) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (255 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (256 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_256 :
    recurrence4A4Square.coeff 256 =
      -(((182752558064251318911874502804192682097 * 10 ^ 70 +
        3736834581292419291420656036119288618057711710514643386020138037414463) * 10 ^ 70 +
        9437015380529109675981557326154620576425926650292556885776285435952631) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (256 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (257 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_257 :
    recurrence4A4Square.coeff 257 =
      (((65007007383412086367735723936935476798 * 10 ^ 70 +
        9662611089418312747624184879602734725596686569083046628504878581217805) * 10 ^ 70 +
        8698238459337009132349756374880349679568335087621790200655851857207338) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (257 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (258 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_258 :
    recurrence4A4Square.coeff 258 =
      -(((22295104583538099814363591962019919249 * 10 ^ 70 +
        1424863237821284784619420427366634535942303070462772977253966768265856) * 10 ^ 70 +
        7559759012614211865089947630288293425897526169911443444847983220682226) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (258 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (259 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_259 :
    recurrence4A4Square.coeff 259 =
      (((7334171452723174731146014079360866816 * 10 ^ 70 +
        0125978382959504597067814839512187395915514793498863362664943324220143) * 10 ^ 70 +
        7577909518695966032947171713225010795242616041436098072408584079576142) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (259 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (260 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_260 :
    recurrence4A4Square.coeff 260 =
      -(((2290867580753899267215172520636134469 * 10 ^ 70 +
        2907822296986258418593987471610610123708437362523472196327337629908544) * 10 ^ 70 +
        4402912408821580925960515963234514536977366939002110623249009866552144) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (260 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (261 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_261 :
    recurrence4A4Square.coeff 261 =
      (((665166819272931587410741094221310527 * 10 ^ 70 +
        7416063421358579756330377165313893199511596426883041110286292243344772) * 10 ^ 70 +
        9582145180662193573835905177002351298983836120114375825878016192420266) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (261 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (262 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_262 :
    recurrence4A4Square.coeff 262 =
      -(((170458667554407295520505928129163860 * 10 ^ 70 +
        2429359770272207102889305070155813801150307332339984176006931379440410) * 10 ^ 70 +
        4923849576166556023455161694652168512836105405508591308468297119384279) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (262 - x)) = _
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
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (263 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_263 :
    recurrence4A4Square.coeff 263 =
      (((32343209955751840269224398128175565 * 10 ^ 70 +
        3966156552588713625613624366046719366396048088429609357518211258295674) * 10 ^ 70 +
        4834350559079847170820194723995366926495289409235890677299496251423624) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (263 - x)) = _
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
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (264 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_264 :
    recurrence4A4Square.coeff 264 =
      (((424327842247054629122606528344247 * 10 ^ 70 +
        2956897354526727039556405152279339230471395581528785080030128168415656) * 10 ^ 70 +
        4603883038758783870797677745465982314531198607413327501891848558267855) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (264 - x)) = _
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
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (265 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_265 :
    recurrence4A4Square.coeff 265 =
      -(((5156434765122720605117203530084609 * 10 ^ 70 +
        9643610314087882190183697372014130333169830756230998937318509477667722) * 10 ^ 70 +
        9924427374790941143511516943066459586506160311723128033726534388002810) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (265 - x)) = _
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
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (266 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_266 :
    recurrence4A4Square.coeff 266 =
      (((3926986961067766470550426793556010 * 10 ^ 70 +
        1161486613839964308525806215300343327325115192936365835096623729060572) * 10 ^ 70 +
        3181105558000728180463220863705797508079537334430031107640641498664827) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (266 - x)) = _
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
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (267 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_267 :
    recurrence4A4Square.coeff 267 =
      -(((2264053692000016079092199177864114 * 10 ^ 70 +
        0174017694976982485987867841279579014824618437698688444732924851669480) * 10 ^ 70 +
        5562147895332512023097829110429083162000191887708794145607685505776382) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (267 - x)) = _
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
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (268 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_268 :
    recurrence4A4Square.coeff 268 =
      (((1157890624054774037667119761868875 * 10 ^ 70 +
        0040844520168753960779614130053879855228073488239902382769447446607660) * 10 ^ 70 +
        6076937046684130295197276011184184818398157550164320931957182239709672) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (268 - x)) = _
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
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (269 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_269 :
    recurrence4A4Square.coeff 269 =
      -(((550644677130346430402569767001389 * 10 ^ 70 +
        8502545217100047341644197395825296025436406237639648255749199853730173) * 10 ^ 70 +
        7295849693696514149744371264515360903570104213859558347638119584665176) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (269 - x)) = _
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
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (270 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_270 :
    recurrence4A4Square.coeff 270 =
      (((247918440393908032496062288544353 * 10 ^ 70 +
        8881994330801484194631800991244827224183764096163661928720190902118182) * 10 ^ 70 +
        9358556686925026661867085373413011873079548592098672873367494150545646) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (270 - x)) = _
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
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (271 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_271 :
    recurrence4A4Square.coeff 271 =
      -(((106398701128939315039237782857771 * 10 ^ 70 +
        7374200466788896383918442549871848837313270040455460086933490785175778) * 10 ^ 70 +
        9735079223596904357419695470048254168236551580166689271090446987987374) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (271 - x)) = _
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
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (272 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_272 :
    recurrence4A4Square.coeff 272 =
      (((43592530608905618360187516329307 * 10 ^ 70 +
        2408147547096942175392759613382114161261831695877230597323258031885604) * 10 ^ 70 +
        2876180190651664937321385319233217514308892555160121125500218671081093) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (272 - x)) = _
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
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (273 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_273 :
    recurrence4A4Square.coeff 273 =
      -(((17024560882164365378638021536230 * 10 ^ 70 +
        3456696192245086027856059826688109515349839787091359051054544693638230) * 10 ^ 70 +
        6179918376392574918768571816775847534020763465665751763481004279073376) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (273 - x)) = _
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
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (274 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_274 :
    recurrence4A4Square.coeff 274 =
      (((6313595267652041714267414899162 * 10 ^ 70 +
        0241993690662354807561082546704081874107523464595282902304389821482125) * 10 ^ 70 +
        8350079805890920095943951191992427827565827650643567583734803376430814) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (274 - x)) = _
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
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (275 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_275 :
    recurrence4A4Square.coeff 275 =
      -(((2209544450645312787362870846500 * 10 ^ 70 +
        5708189127529489478849469959835526005970831265466301706189464295625863) * 10 ^ 70 +
        0069652939985572293704122443571372554836564664277109233951834147419492) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (275 - x)) = _
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
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (276 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_276 :
    recurrence4A4Square.coeff 276 =
      (((722577472554235050082938608506 * 10 ^ 70 +
        3775887527901364549921129380987940726424170237982345273130430874196577) * 10 ^ 70 +
        3373891627297531773483570474773421130822307338946494187339008414239055) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (276 - x)) = _
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
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (277 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_277 :
    recurrence4A4Square.coeff 277 =
      -(((217215955554990834236777202409 * 10 ^ 70 +
        2646356862113469060279649431721257025113227571147558399698569884379493) * 10 ^ 70 +
        4767660983995530661790002899737793609578418268793299419312033337232332) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (277 - x)) = _
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
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (278 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_278 :
    recurrence4A4Square.coeff 278 =
      (((58186368348956106168888862718 * 10 ^ 70 +
        9191682092688179667452230630317489875765623863933950907402351999092447) * 10 ^ 70 +
        8393267785659121438264355260460151666374330561393560272747595026944948) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (278 - x)) = _
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
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (279 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_279 :
    recurrence4A4Square.coeff 279 =
      -(((12905931283503570123803351408 * 10 ^ 70 +
        9675115328719241106117701239065243853307322559995838989447548090054355) * 10 ^ 70 +
        6654199794177137893054266716335010079749968438496122826185023396361562) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (279 - x)) = _
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
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (280 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_280 :
    recurrence4A4Square.coeff 280 =
      (((1794557209716433293654742641 * 10 ^ 70 +
        4969638033672432542154865183536163352113706601556875623619304218813293) * 10 ^ 70 +
        3777809508752058976464882131064898402801653804979942920627630352224759) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (280 - x)) = _
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
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (281 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_281 :
    recurrence4A4Square.coeff 281 =
      (((244785599943422337929280395 * 10 ^ 70 +
        6781484951184627586482320229335687926170149681698346614706191595003797) * 10 ^ 70 +
        2037731931613561594563042561568510032898283860650635105648011826071954) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (281 - x)) = _
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
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (282 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_282 :
    recurrence4A4Square.coeff 282 =
      -(((326600351085050430358689152 * 10 ^ 70 +
        0521701596221820382243467582019039399564134987622052959885840025263386) * 10 ^ 70 +
        8116325332156284113931686214603381843760013859405319404857999469798419) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (282 - x)) = _
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
    rw [show 115 = 11 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (283 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_283 :
    recurrence4A4Square.coeff 283 =
      (((167640772833160863247047263 * 10 ^ 70 +
        4360305673167277817940981790743257446667037058393323873752334769314684) * 10 ^ 70 +
        1502267367399127798402459602720354853915635015894945106144274782991822) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (283 - x)) = _
  rw [show 284 = 105 +
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
  rw [recurrence4A4Square_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (284 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_284 :
    recurrence4A4Square.coeff 284 =
      -(((65651846528189018273312465 * 10 ^ 70 +
        0222957886584490560603238205096307477561316492769620927048641016172180) * 10 ^ 70 +
        6009413692020685033269394103124955285338477129407190935236817218499485) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (284 - x)) = _
  rw [show 285 = 106 +
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
  rw [recurrence4A4Square_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
