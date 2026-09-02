/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2ExceptionalProduct_coeff_0
  recurrence2ExceptionalProduct_coeff_1
  recurrence2ExceptionalProduct_coeff_2
  recurrence2ExceptionalProduct_coeff_3
  recurrence2ExceptionalProduct_coeff_4
  recurrence2ExceptionalProduct_coeff_5
  recurrence2ExceptionalProduct_coeff_6
  recurrence2ExceptionalProduct_coeff_7
  recurrence2ExceptionalProduct_coeff_8
  recurrence2ExceptionalProduct_coeff_9
  recurrence2ExceptionalProduct_coeff_10
  recurrence2ExceptionalProduct_coeff_11
  recurrence2ExceptionalProduct_coeff_12
  recurrence2ExceptionalProduct_coeff_13
  recurrence2ExceptionalProduct_coeff_14
  recurrence2ExceptionalProduct_coeff_15
  recurrence2ExceptionalProduct_coeff_16
  recurrence2ExceptionalProduct_coeff_17
  recurrence2ExceptionalProduct_coeff_18
  recurrence2ExceptionalProduct_coeff_19
  recurrence2ExceptionalProduct_coeff_20
  recurrence2ExceptionalProduct_coeff_21
  recurrence2ExceptionalProduct_coeff_22
  recurrence2ExceptionalProduct_coeff_23
  recurrence2ExceptionalProduct_coeff_24
  recurrence2ExceptionalProduct_coeff_25
  recurrence2ExceptionalProduct_coeff_26
  recurrence2ExceptionalProduct_coeff_27
  recurrence2ExceptionalProduct_coeff_28
  recurrence2ExceptionalProduct_coeff_29
  recurrence2ExceptionalProduct_coeff_30
  recurrence2ExceptionalProduct_coeff_31
  recurrence2ExceptionalProduct_coeff_32
  recurrence2ExceptionalProduct_coeff_33
  recurrence2ExceptionalProduct_coeff_34
  recurrence2ExceptionalProduct_coeff_35
  recurrence2ExceptionalProduct_coeff_36
  recurrence2ExceptionalProduct_coeff_37
  recurrence2ExceptionalProduct_coeff_38
  recurrence2ExceptionalProduct_coeff_39
  recurrence2ExceptionalProduct_coeff_40
  recurrence2ExceptionalProduct_coeff_41
  recurrence2ExceptionalProduct_coeff_42
  recurrence2ExceptionalProduct_coeff_43
  recurrence2ExceptionalProduct_coeff_44
  recurrence2ExceptionalProduct_coeff_45
  recurrence2ExceptionalProduct_coeff_46
  recurrence2ExceptionalProduct_coeff_47
  recurrence2ExceptionalProduct_coeff_48
  recurrence2ExceptionalProduct_coeff_49
  recurrence2ExceptionalProduct_coeff_50
  recurrence2ExceptionalProduct_coeff_51
  recurrence2ExceptionalProduct_coeff_52
  recurrence2ExceptionalProduct_coeff_53
  recurrence2ExceptionalProduct_coeff_54
  recurrence2ExceptionalProduct_coeff_55
  recurrence2ExceptionalProduct_coeff_56
  recurrence2ExceptionalProduct_coeff_57
  recurrence2ExceptionalProduct_coeff_58
  recurrence2ExceptionalProduct_coeff_59
  recurrence2ExceptionalProduct_coeff_60
  recurrence2ExceptionalProduct_coeff_61
  recurrence2ExceptionalProduct_coeff_62
  recurrence2ExceptionalProduct_coeff_63
  recurrence2ExceptionalProduct_coeff_64
  recurrence2ExceptionalProduct_coeff_65
  recurrence2ExceptionalProduct_coeff_66
  recurrence2ExceptionalProduct_coeff_67
  recurrence2ExceptionalProduct_coeff_68
  recurrence2ExceptionalProduct_coeff_69
  recurrence2ExceptionalProduct_coeff_70
  recurrence2ExceptionalProduct_coeff_71
  recurrence2ExceptionalProduct_coeff_72
  recurrence2ExceptionalProduct_coeff_73
  recurrence2ExceptionalProduct_coeff_74
  recurrence2ExceptionalProduct_coeff_75
  recurrence2ExceptionalProduct_coeff_76
  recurrence2ExceptionalProduct_coeff_77
  recurrence2ExceptionalProduct_coeff_78
  recurrence2ExceptionalProduct_coeff_79
  recurrence2ExceptionalProduct_coeff_80
  recurrence2ExceptionalProduct_coeff_81
  recurrence2ExceptionalProduct_coeff_82
  recurrence2ExceptionalProduct_coeff_83
  recurrence2ExceptionalProduct_coeff_84
  recurrence2ExceptionalProduct_coeff_85
  recurrence2ExceptionalProduct_coeff_86
  recurrence2ExceptionalProduct_coeff_87
  recurrence2ExceptionalProduct_coeff_88
  recurrence2ExceptionalProduct_coeff_89
  recurrence2ExceptionalProduct_coeff_90
  recurrence2ExceptionalProduct_coeff_91
  recurrence2ExceptionalProduct_coeff_92
  recurrence2ExceptionalProduct_coeff_93
  recurrence2ExceptionalProduct_coeff_94
  recurrence2ExceptionalProduct_coeff_95
  recurrence2ExceptionalProduct_coeff_96
  recurrence2ExceptionalProduct_coeff_97
  recurrence2ExceptionalProduct_coeff_98
  recurrence2ExceptionalProduct_coeff_99
  recurrence2ExceptionalProduct_coeff_100
  recurrence2ExceptionalProduct_coeff_101
  recurrence2ExceptionalProduct_coeff_102
  recurrence2ExceptionalProduct_coeff_103
  recurrence2ExceptionalProduct_coeff_104
  recurrence2ExceptionalProduct_coeff_105
  recurrence2ExceptionalProduct_coeff_106
  recurrence2ExceptionalProduct_coeff_107
  recurrence2ExceptionalProduct_coeff_108
  recurrence2ExceptionalProduct_coeff_109
  recurrence2ExceptionalProduct_coeff_110
  recurrence2ExceptionalProduct_coeff_111
  recurrence2ExceptionalProduct_coeff_112
  recurrence2ExceptionalProduct_coeff_113
  recurrence2ExceptionalProduct_coeff_114
  recurrence2ExceptionalProduct_coeff_115
  recurrence2ExceptionalProduct_coeff_116
  recurrence2ExceptionalProduct_coeff_117
  recurrence2ExceptionalProduct_coeff_118
  recurrence2ExceptionalProduct_coeff_119
  recurrence2ExceptionalProduct_coeff_120
  recurrence2ExceptionalProduct_coeff_121
  recurrence2ExceptionalProduct_coeff_122
  recurrence2ExceptionalProduct_coeff_123
  recurrence2ExceptionalProduct_coeff_124
  recurrence2ExceptionalProduct_coeff_125
  recurrence2ExceptionalProduct_coeff_126
  recurrence2ExceptionalProduct_coeff_127
  recurrence2ExceptionalProduct_coeff_128
  recurrence2ExceptionalProduct_coeff_129
  recurrence2ExceptionalProduct_coeff_130
  recurrence2ExceptionalProduct_coeff_131
  recurrence2ExceptionalProduct_coeff_132
  recurrence2ExceptionalProduct_coeff_133
  recurrence2ExceptionalProduct_coeff_134
  recurrence2ExceptionalProduct_coeff_135
  recurrence2ExceptionalProduct_coeff_136
  recurrence2ExceptionalProduct_coeff_137
  recurrence2ExceptionalProduct_coeff_138
  recurrence2ExceptionalProduct_coeff_139
  recurrence2ExceptionalProduct_coeff_140
  recurrence2ExceptionalProduct_coeff_141
  recurrence2ExceptionalProduct_coeff_142
  recurrence2ExceptionalProduct_coeff_143
  recurrence2ExceptionalProduct_coeff_144
  recurrence2ExceptionalProduct_coeff_145
  recurrence2ExceptionalProduct_coeff_146
  recurrence2ExceptionalProduct_coeff_147
  recurrence2ExceptionalProduct_coeff_148
  recurrence2ExceptionalProduct_coeff_149
  recurrence2ExceptionalProduct_coeff_150
  recurrence2ExceptionalProduct_coeff_151
  recurrence2ExceptionalProduct_coeff_152
  recurrence2ExceptionalProduct_coeff_153
  recurrence2ExceptionalProduct_coeff_154
  recurrence2ExceptionalProduct_coeff_155
  recurrence2ExceptionalProduct_coeff_156
  recurrence2ExceptionalProduct_coeff_157
  recurrence2ExceptionalProduct_coeff_158
  recurrence2ExceptionalProduct_coeff_159
  recurrence2ExceptionalProduct_coeff_160
  recurrence2ExceptionalProduct_coeff_161
  recurrence2ExceptionalProduct_coeff_162
  recurrence2ExceptionalProduct_coeff_163
  recurrence2ExceptionalProduct_coeff_164
  recurrence2ExceptionalProduct_coeff_165
  recurrence2ExceptionalProduct_coeff_166
  recurrence2ExceptionalProduct_coeff_167
  recurrence2ExceptionalProduct_coeff_168
  recurrence2ExceptionalProduct_coeff_169
  recurrence2ExceptionalProduct_coeff_170
  recurrence2ExceptionalProduct_coeff_171
  recurrence2ExceptionalProduct_coeff_172
  recurrence2ExceptionalProduct_coeff_173
  recurrence2ExceptionalProduct_coeff_174
  recurrence2ExceptionalProduct_coeff_175
  recurrence2ExceptionalProduct_coeff_176
  recurrence2ExceptionalProduct_coeff_177
  recurrence2ExceptionalProduct_coeff_178
  recurrence2ExceptionalProduct_coeff_179
  recurrence2ExceptionalProduct_coeff_180
  recurrence2ExceptionalProduct_coeff_181
  recurrence2ExceptionalProduct_coeff_182
  recurrence2ExceptionalProduct_coeff_183
  recurrence2ExceptionalProduct_coeff_184
  recurrence2ExceptionalProduct_coeff_185
  recurrence2ExceptionalProduct_coeff_186
  recurrence2ExceptionalProduct_coeff_187
  recurrence2ExceptionalProduct_coeff_188
  recurrence2ExceptionalProduct_coeff_189
  recurrence2ExceptionalProduct_coeff_190
  recurrence2ExceptionalProduct_coeff_191
  recurrence2ExceptionalProduct_coeff_192
  recurrence2ExceptionalProduct_coeff_193
  recurrence2C0_coeff_0
  recurrence2C0_coeff_1
  recurrence2C0_coeff_2
  recurrence2C0_coeff_3
  recurrence2C0_coeff_4
  recurrence2C0_coeff_5
  recurrence2C0_coeff_6
  recurrence2C0_coeff_7
  recurrence2C0_coeff_8
  recurrence2C0_coeff_9
  recurrence2C0_coeff_10
  recurrence2C0_coeff_11
  recurrence2C0_coeff_12
  recurrence2C0_coeff_13
  recurrence2C0_coeff_14
  recurrence2C0_coeff_15
  recurrence2C0_coeff_16
  recurrence2C0_coeff_17
  recurrence2C0_coeff_18
  recurrence2C0_coeff_19
  recurrence2C0_coeff_20
  recurrence2C0_coeff_21
  recurrence2C0_coeff_22
  recurrence2C0_coeff_23
  recurrence2C0_coeff_24
  recurrence2C0_coeff_25
  recurrence2C0_coeff_26
  recurrence2C0_coeff_27
  recurrence2C0_coeff_28
  recurrence2C0_coeff_29
  recurrence2C0_coeff_30
  recurrence2C0_coeff_31
  recurrence2C0_coeff_32
  recurrence2C0_coeff_33
  recurrence2C0_coeff_34
  recurrence2C0_coeff_35
  recurrence2C0_coeff_36
  recurrence2C0_coeff_37
  recurrence2C0_coeff_38
  recurrence2C0_coeff_39
  recurrence2C0_coeff_40
  recurrence2C0_coeff_41
  recurrence2C0_coeff_42
  recurrence2C0_coeff_43
  recurrence2C0_coeff_44
  recurrence2C0_coeff_45
  recurrence2C0_coeff_46
  recurrence2C0_coeff_47
  recurrence2C0_coeff_48
  recurrence2C0_coeff_49
  recurrence2C0_coeff_50
  recurrence2C0_coeff_51
  recurrence2C0_coeff_52
  recurrence2C0_coeff_53
  recurrence2C0_coeff_54
  recurrence2C0_coeff_55
  recurrence2C0_coeff_56
  recurrence2C0_coeff_57
  recurrence2C0_coeff_58
  recurrence2C0_coeff_59
  recurrence2C0_coeff_60
  recurrence2C0_coeff_61
  recurrence2C0_coeff_62
  recurrence2C0_coeff_63
  recurrence2C0_coeff_64
  recurrence2C0_coeff_65
  recurrence2C0_coeff_66
  recurrence2C0_coeff_67
  recurrence2C0_coeff_68
  recurrence2C0_coeff_69
  recurrence2C0_coeff_70
  recurrence2C0_coeff_71
  recurrence2C0_coeff_72
  recurrence2C0_coeff_73
  recurrence2C0_coeff_74
  recurrence2C0_coeff_75
  recurrence2C0_coeff_76
  recurrence2C0_coeff_77
  recurrence2C0_coeff_78
  recurrence2C0_coeff_79
  recurrence2C0_coeff_80
  recurrence2C0_coeff_81
  recurrence2C0_coeff_82
  recurrence2C0_coeff_83
  recurrence2C0_coeff_84
  recurrence2C0_coeff_85
  recurrence2C0_coeff_86
  recurrence2C0_coeff_87
  recurrence2C0_coeff_88
  recurrence2C0_coeff_89
  recurrence2C0_coeff_90
  recurrence2C0_coeff_91
  recurrence2C0_coeff_92
  recurrence2C0_coeff_93
  recurrence2C0_coeff_94
  recurrence2C0_coeff_95
  recurrence2C0_coeff_96
  recurrence2C0_coeff_97
  recurrence2C0_coeff_98
  recurrence2C0_coeff_99
  recurrence2C0_coeff_100
  recurrence2C0_coeff_101
  recurrence2C0_coeff_102
  recurrence2C0_coeff_103
  recurrence2C0_coeff_104
  recurrence2C0_coeff_105
  recurrence2C0_coeff_106
  recurrence2C0_coeff_107
  recurrence2C0_coeff_108
  recurrence2C0_coeff_109
  recurrence2C0_coeff_110
  recurrence2C0_coeff_111
  recurrence2C0_coeff_112
  recurrence2C0_coeff_113
  recurrence2C0_coeff_114
  recurrence2C0_coeff_115
  recurrence2C0_coeff_116
  recurrence2C0_coeff_117
  recurrence2C0_coeff_118
  recurrence2C0_coeff_119
  recurrence2C0_coeff_120
  recurrence2C0_coeff_121
  recurrence2C0_coeff_122
  recurrence2C0_coeff_123
  recurrence2C0_coeff_124
  recurrence2C0_coeff_125
  recurrence2C0_coeff_126
  recurrence2C0_coeff_127
  recurrence2C0_coeff_128
  recurrence2C0_coeff_129
  recurrence2C0_coeff_130
  recurrence2C0_coeff_131
  recurrence2C0_coeff_132
  recurrence2C0_coeff_133
  recurrence2C0_coeff_134
  recurrence2C0_coeff_135
  recurrence2C0_coeff_136
  recurrence2C0_coeff_137
  recurrence2C0_coeff_138
  recurrence2C0_coeff_139
  recurrence2C0_coeff_140
  recurrence2C0_coeff_141
  recurrence2C0_coeff_142
  recurrence2C0_coeff_143
  recurrence2C0_coeff_144
  recurrence2C0_coeff_145
  recurrence2C0_coeff_146
  recurrence2C0_coeff_147
  recurrence2C0_coeff_148
  recurrence2C0_coeff_149
  recurrence2C0_coeff_150
  recurrence2C0_coeff_151
  recurrence2C0_coeff_152
  recurrence2C0_coeff_153
  recurrence2C0_coeff_154
  recurrence2C0_coeff_155
  recurrence2C0_coeff_156
  recurrence2C0_coeff_157
  recurrence2C0_coeff_158
  recurrence2C0_coeff_159
  recurrence2C0_coeff_160
  recurrence2C0_coeff_161
  recurrence2C0_coeff_162
  recurrence2C0_coeff_163
  recurrence2C0_coeff_164
  recurrence2C0_coeff_165
  recurrence2C0_coeff_166
  recurrence2C0_coeff_167
  recurrence2C0_coeff_168
  recurrence2C0_coeff_169
  recurrence2C0_coeff_170
  recurrence2C0_coeff_171
  recurrence2C0_coeff_172
  recurrence2C0_coeff_173
  recurrence2C0_coeff_174
  recurrence2C0_coeff_175
  recurrence2C0_coeff_176
  recurrence2C0_coeff_177
  recurrence2C0_coeff_178
  recurrence2C0_coeff_179
  recurrence2C0_coeff_180
  recurrence2C0_coeff_181
  recurrence2C0_coeff_182
  recurrence2C0_coeff_183
  recurrence2C0_coeff_184
  recurrence2C0_coeff_185
  recurrence2C0_coeff_186
  recurrence2C0_coeff_187
  recurrence2C0_coeff_188
  recurrence2C0_coeff_189
  recurrence2C0_coeff_190
  recurrence2C0_coeff_191
  recurrence2C0_coeff_192
  recurrence2C0_coeff_193
  recurrence2C0_coeff_194

private theorem recurrence2Scalar0Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_285 :
    recurrence2Scalar0Exceptional.coeff 285 =
      -(((9031232310568192897131610957578057198865019450 * 10 ^ 70 +
        2662371373671294440274674428674269108397055956142748752155058926769049) * 10 ^ 70 +
        7608449550739387918509485329317118674558178599646699118188875957996879) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 91 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 7 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_286 :
    recurrence2Scalar0Exceptional.coeff 286 =
      (((3477257079003777260064689037241071226900479260 * 10 ^ 70 +
        6095479396473462921932381510295652267809260132587383921198669092308462) * 10 ^ 70 +
        7858914435787439795741445636255729333234560058204688745758693639694881) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 92 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 6 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_287 :
    recurrence2Scalar0Exceptional.coeff 287 =
      -(((986275830818298752758092396506938294725165949 * 10 ^ 70 +
        5634176197444832250829302094734285377117475798383179538302867860109845) * 10 ^ 70 +
        9220014701956661578098856281207397712063949328524514589173784713174708) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 93 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 5 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_288 :
    recurrence2Scalar0Exceptional.coeff 288 =
      (((103850703629986681979282755359676384366684092 * 10 ^ 70 +
        5596555828303277517139198072472081587117172196145451666234070783467908) * 10 ^ 70 +
        9757008319189099139296390023131492428869450348526069389520495913318783) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 94 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 4 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_289 :
    recurrence2Scalar0Exceptional.coeff 289 =
      (((100661751106653770208312736912618390366410038 * 10 ^ 70 +
        7495907397546604558727506657402136591691156522505803730563662522087096) * 10 ^ 70 +
        0333593146892745385523690800375432841084639549877943100050005595777577) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 95 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 3 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_290 :
    recurrence2Scalar0Exceptional.coeff 290 =
      -(((91217586290464130543062067134602829982008443 * 10 ^ 70 +
        4471209121708100428812089915851868167275703882058793971280854146557444) * 10 ^ 70 +
        5230797157591983674153969606999049861192196358706057451226798154098679) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 96 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 2 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_291 :
    recurrence2Scalar0Exceptional.coeff 291 =
      (((47903544903716036279216274404310002323703278 * 10 ^ 70 +
        4154938504842652253166472969777628014886024867747404867168961424166909) * 10 ^ 70 +
        8805630597305702067368711106284803157583361399726483135687383930625474) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 97 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 1 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_292 :
    recurrence2Scalar0Exceptional.coeff 292 =
      -(((18595438731048746520761380851909616899031612 * 10 ^ 70 +
        5495310638448737661057883975102574746030906298841309810790551072767011) * 10 ^ 70 +
        4831013470547463962251017780513033270705874698485280474646089386716687) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 98 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_293 :
    recurrence2Scalar0Exceptional.coeff 293 =
      (((5271779662193762877330367265046517329799434 * 10 ^ 70 +
        5427889256990116159752114690984952586223946682102525878947802225218057) * 10 ^ 70 +
        1898876802353891133302084449323078667903459119330077056848327629678256) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 99 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 31 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_294 :
    recurrence2Scalar0Exceptional.coeff 294 =
      -(((794523697022878238783776881660381150954330 * 10 ^ 70 +
        7284522775989033209640218057276114916889567933207312218413715595459812) * 10 ^ 70 +
        1532126486036928427063551416924358409669439940687286378457950174480554) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 100 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 30 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_295 :
    recurrence2Scalar0Exceptional.coeff 295 =
      -(((198203704580831704598501712582600197177937 * 10 ^ 70 +
        2623216497966687838509697371019125596890166890831417372336403916590900) * 10 ^ 70 +
        0760033362882206157288525575316036479882249296198776181306236709339660) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 101 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 29 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_296 :
    recurrence2Scalar0Exceptional.coeff 296 =
      (((215748273008172603621773961899480104855558 * 10 ^ 70 +
        2485234301596296015964767060648101316398562402442504050237575935649864) * 10 ^ 70 +
        2817199018859368089769956584969745669279272075654846788614137199207480) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 102 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 28 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_297 :
    recurrence2Scalar0Exceptional.coeff 297 =
      -(((100692873916926646330089868069434533161361 * 10 ^ 70 +
        5529700539999993557873720901575870089476083147863123012555643205116964) * 10 ^ 70 +
        2011616498177950290705961948294610954475941588076903873321426782271163) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 103 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 27 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_298 :
    recurrence2Scalar0Exceptional.coeff 298 =
      (((31950088344221728331244176872123347775449 * 10 ^ 70 +
        5299048596238384920926540688202158934586499668657283361439796694303106) * 10 ^ 70 +
        1340587463618238639936696356966238421607444062079018297218386822218763) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 104 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 26 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_299 :
    recurrence2Scalar0Exceptional.coeff 299 =
      -(((6538342611127800872809271026431956234167 * 10 ^ 70 +
        2792743386416239208887967765063396248482801432409480640915075426036644) * 10 ^ 70 +
        3424164830566510864224150598657292604170879616501940518535313476292325) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 105 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 25 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_300 :
    recurrence2Scalar0Exceptional.coeff 300 =
      (((195346873959921214974951757954154271113 * 10 ^ 70 +
        1607528453295162297085808654324438265477703552488520205101835019975345) * 10 ^ 70 +
        6664298938202483918145487706669106283553679420179065478560060169913319) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 106 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 24 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_301 :
    recurrence2Scalar0Exceptional.coeff 301 =
      (((524088084362626649751119389742499092420 * 10 ^ 70 +
        9956310096478604304268089175870979376546918729522970983261498996295996) * 10 ^ 70 +
        7809131425629601236038630738740811445958867164135083967823506525852527) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 107 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 23 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_302 :
    recurrence2Scalar0Exceptional.coeff 302 =
      -(((272293275653152659394566600786884558945 * 10 ^ 70 +
        2897486058980761110957307644528768819622109518901978403694546134688495) * 10 ^ 70 +
        8980706938189558512163728404069629099417745553698420195262383193788393) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 108 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 22 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_303 :
    recurrence2Scalar0Exceptional.coeff 303 =
      (((82962591607376042739630291343450871259 * 10 ^ 70 +
        3779109103804788843966776640860806357351239735177821068822013777481237) * 10 ^ 70 +
        8844982610309197570766560094758787220342387066632703543488691702913680) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 109 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 21 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_304 :
    recurrence2Scalar0Exceptional.coeff 304 =
      -(((15525885817255860421272834562664625061 * 10 ^ 70 +
        2732770046042193445143300246195695767380951876791326364552053100373210) * 10 ^ 70 +
        8776690490029578691308798137841629086871530083458131722163171321968608) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 110 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 20 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_305 :
    recurrence2Scalar0Exceptional.coeff 305 =
      (((426122416542210317160255980390437656 * 10 ^ 70 +
        0108906338716468382509756635196492258230581715368625470085966091559292) * 10 ^ 70 +
        3616215521972990692748227173661311015465488313882879476285291522612644) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 111 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 19 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_306 :
    recurrence2Scalar0Exceptional.coeff 306 =
      (((944606842636181125558460104942465837 * 10 ^ 70 +
        8185476352513757009266797602350928494235115624177354222318509114701514) * 10 ^ 70 +
        9421853854548005642767708925159626467285490903447112184580444400185441) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 112 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 18 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_307 :
    recurrence2Scalar0Exceptional.coeff 307 =
      -(((411696224307459583803238131256290741 * 10 ^ 70 +
        8182973858416140219153691222650716096493821345630323581138935581872638) * 10 ^ 70 +
        8572859317881720392472504468549391090226855350325059228126110866904305) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 113 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 17 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_308 :
    recurrence2Scalar0Exceptional.coeff 308 =
      (((99434259403802749164378602763887267 * 10 ^ 70 +
        7170035148039052319025121947236304447322443504285379808295445405591430) * 10 ^ 70 +
        1410043848723277539288591596521761956006704820850653388322298365504199) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 114 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 16 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_309 :
    recurrence2Scalar0Exceptional.coeff 309 =
      -(((12190566843226861165395506277678649 * 10 ^ 70 +
        5505003720308630404880990305220618047048735927870662792270541818654341) * 10 ^ 70 +
        5134196617561270954575450100737261715161136602995627947783200507610872) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 115 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 15 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_310 :
    recurrence2Scalar0Exceptional.coeff 310 =
      -(((1305617410328489646504263538053352 * 10 ^ 70 +
        4544752423295079043346673483604158094172882242815036534286300918557696) * 10 ^ 70 +
        3818201367311048955288348304712251590713382348161852392946272142572007) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 116 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 14 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_311 :
    recurrence2Scalar0Exceptional.coeff 311 =
      (((1101622057683942146512656942553104 * 10 ^ 70 +
        2337372735550455929594088210047941481070829327955075358841828471022175) * 10 ^ 70 +
        7401141827765621376617205228678533106316732087319622748197714726705463) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 117 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 13 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_312 :
    recurrence2Scalar0Exceptional.coeff 312 =
      -(((295656816215071070914874682356595 * 10 ^ 70 +
        6879101434023321750369482856104792505803201698657724141673237385949718) * 10 ^ 70 +
        8033388181600019908924709544598112590028994458310253387742267906563791) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 118 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 12 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
