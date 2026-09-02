/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Exceptional coefficient convolution

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
  recurrence2C1_coeff_0
  recurrence2C1_coeff_1
  recurrence2C1_coeff_2
  recurrence2C1_coeff_3
  recurrence2C1_coeff_4
  recurrence2C1_coeff_5
  recurrence2C1_coeff_6
  recurrence2C1_coeff_7
  recurrence2C1_coeff_8
  recurrence2C1_coeff_9
  recurrence2C1_coeff_10
  recurrence2C1_coeff_11
  recurrence2C1_coeff_12
  recurrence2C1_coeff_13
  recurrence2C1_coeff_14
  recurrence2C1_coeff_15
  recurrence2C1_coeff_16
  recurrence2C1_coeff_17
  recurrence2C1_coeff_18
  recurrence2C1_coeff_19
  recurrence2C1_coeff_20
  recurrence2C1_coeff_21
  recurrence2C1_coeff_22
  recurrence2C1_coeff_23
  recurrence2C1_coeff_24
  recurrence2C1_coeff_25
  recurrence2C1_coeff_26
  recurrence2C1_coeff_27
  recurrence2C1_coeff_28
  recurrence2C1_coeff_29
  recurrence2C1_coeff_30
  recurrence2C1_coeff_31
  recurrence2C1_coeff_32
  recurrence2C1_coeff_33
  recurrence2C1_coeff_34
  recurrence2C1_coeff_35
  recurrence2C1_coeff_36
  recurrence2C1_coeff_37
  recurrence2C1_coeff_38
  recurrence2C1_coeff_39
  recurrence2C1_coeff_40
  recurrence2C1_coeff_41
  recurrence2C1_coeff_42
  recurrence2C1_coeff_43
  recurrence2C1_coeff_44
  recurrence2C1_coeff_45
  recurrence2C1_coeff_46
  recurrence2C1_coeff_47
  recurrence2C1_coeff_48
  recurrence2C1_coeff_49
  recurrence2C1_coeff_50
  recurrence2C1_coeff_51
  recurrence2C1_coeff_52
  recurrence2C1_coeff_53
  recurrence2C1_coeff_54
  recurrence2C1_coeff_55
  recurrence2C1_coeff_56
  recurrence2C1_coeff_57
  recurrence2C1_coeff_58
  recurrence2C1_coeff_59
  recurrence2C1_coeff_60
  recurrence2C1_coeff_61
  recurrence2C1_coeff_62
  recurrence2C1_coeff_63
  recurrence2C1_coeff_64
  recurrence2C1_coeff_65
  recurrence2C1_coeff_66
  recurrence2C1_coeff_67
  recurrence2C1_coeff_68
  recurrence2C1_coeff_69
  recurrence2C1_coeff_70
  recurrence2C1_coeff_71
  recurrence2C1_coeff_72
  recurrence2C1_coeff_73
  recurrence2C1_coeff_74
  recurrence2C1_coeff_75
  recurrence2C1_coeff_76
  recurrence2C1_coeff_77
  recurrence2C1_coeff_78
  recurrence2C1_coeff_79
  recurrence2C1_coeff_80
  recurrence2C1_coeff_81
  recurrence2C1_coeff_82
  recurrence2C1_coeff_83
  recurrence2C1_coeff_84
  recurrence2C1_coeff_85
  recurrence2C1_coeff_86
  recurrence2C1_coeff_87
  recurrence2C1_coeff_88
  recurrence2C1_coeff_89
  recurrence2C1_coeff_90
  recurrence2C1_coeff_91
  recurrence2C1_coeff_92
  recurrence2C1_coeff_93
  recurrence2C1_coeff_94
  recurrence2C1_coeff_95
  recurrence2C1_coeff_96
  recurrence2C1_coeff_97
  recurrence2C1_coeff_98
  recurrence2C1_coeff_99
  recurrence2C1_coeff_100
  recurrence2C1_coeff_101
  recurrence2C1_coeff_102
  recurrence2C1_coeff_103
  recurrence2C1_coeff_104
  recurrence2C1_coeff_105
  recurrence2C1_coeff_106
  recurrence2C1_coeff_107
  recurrence2C1_coeff_108
  recurrence2C1_coeff_109
  recurrence2C1_coeff_110
  recurrence2C1_coeff_111
  recurrence2C1_coeff_112
  recurrence2C1_coeff_113
  recurrence2C1_coeff_114
  recurrence2C1_coeff_115
  recurrence2C1_coeff_116
  recurrence2C1_coeff_117
  recurrence2C1_coeff_118
  recurrence2C1_coeff_119
  recurrence2C1_coeff_120
  recurrence2C1_coeff_121
  recurrence2C1_coeff_122
  recurrence2C1_coeff_123
  recurrence2C1_coeff_124
  recurrence2C1_coeff_125
  recurrence2C1_coeff_126
  recurrence2C1_coeff_127
  recurrence2C1_coeff_128
  recurrence2C1_coeff_129
  recurrence2C1_coeff_130
  recurrence2C1_coeff_131
  recurrence2C1_coeff_132
  recurrence2C1_coeff_133
  recurrence2C1_coeff_134
  recurrence2C1_coeff_135
  recurrence2C1_coeff_136
  recurrence2C1_coeff_137
  recurrence2C1_coeff_138
  recurrence2C1_coeff_139
  recurrence2C1_coeff_140
  recurrence2C1_coeff_141
  recurrence2C1_coeff_142
  recurrence2C1_coeff_143
  recurrence2C1_coeff_144
  recurrence2C1_coeff_145
  recurrence2C1_coeff_146
  recurrence2C1_coeff_147
  recurrence2C1_coeff_148
  recurrence2C1_coeff_149
  recurrence2C1_coeff_150
  recurrence2C1_coeff_151
  recurrence2C1_coeff_152
  recurrence2C1_coeff_153
  recurrence2C1_coeff_154
  recurrence2C1_coeff_155
  recurrence2C1_coeff_156
  recurrence2C1_coeff_157
  recurrence2C1_coeff_158
  recurrence2C1_coeff_159
  recurrence2C1_coeff_160
  recurrence2C1_coeff_161
  recurrence2C1_coeff_162
  recurrence2C1_coeff_163
  recurrence2C1_coeff_164
  recurrence2C1_coeff_165
  recurrence2C1_coeff_166
  recurrence2C1_coeff_167
  recurrence2C1_coeff_168
  recurrence2C1_coeff_169
  recurrence2C1_coeff_170
  recurrence2C1_coeff_171
  recurrence2C1_coeff_172
  recurrence2C1_coeff_173
  recurrence2C1_coeff_174
  recurrence2C1_coeff_175
  recurrence2C1_coeff_176
  recurrence2C1_coeff_177
  recurrence2C1_coeff_178
  recurrence2C1_coeff_179
  recurrence2C1_coeff_180
  recurrence2C1_coeff_181
  recurrence2C1_coeff_182
  recurrence2C1_coeff_183
  recurrence2C1_coeff_184
  recurrence2C1_coeff_185
  recurrence2C1_coeff_186
  recurrence2C1_coeff_187
  recurrence2C1_coeff_188
  recurrence2C1_coeff_189
  recurrence2C1_coeff_190

private theorem recurrence2Scalar1Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_258 :
    recurrence2Scalar1Exceptional.coeff 258 =
      (((2184504747302033324609489690037910445968791251494253031 * 10 ^ 70 +
        8565184718945359895369245920553849685734027485612823929751403890005181) * 10 ^ 70 +
        3769704277420895987258408779091034289077513005783103317078566877167788) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 68 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 30 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_259 :
    recurrence2Scalar1Exceptional.coeff 259 =
      -(((1041323194739635889152635728146647646142197149590036152 * 10 ^ 70 +
        9686131573889654408382644591584142823718657765580226728103671256940674) * 10 ^ 70 +
        5623303912801487187190498773413235952484304094101006904849815910731325) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 69 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 29 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_260 :
    recurrence2Scalar1Exceptional.coeff 260 =
      (((437485109783086109324328819578783940844124188355283752 * 10 ^ 70 +
        0211549899714733960178859587918410030841059292063669036010916709475185) * 10 ^ 70 +
        5328036573742044835069347922686042052852856165127070691550948197090890) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 70 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 28 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_261 :
    recurrence2Scalar1Exceptional.coeff 261 =
      -(((163528573869556786987501643177639995215158899188376891 * 10 ^ 70 +
        7080782411018406459000983267156617725706761144832932711266933527438477) * 10 ^ 70 +
        5747615479992819946122494914531105758032335227052031749518220731850624) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 71 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 27 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_262 :
    recurrence2Scalar1Exceptional.coeff 262 =
      (((53840021776045105093614988561267078939944661601380319 * 10 ^ 70 +
        6076559244940886787501094057448233539888418019840326392488433639364562) * 10 ^ 70 +
        7911467316689193089384972757077834810848307287170601665051463330510473) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 72 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 26 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_263 :
    recurrence2Scalar1Exceptional.coeff 263 =
      -(((14802253981067972504934982362924926887124053429634696 * 10 ^ 70 +
        5757214249684831360133696255638898715893700560921934978684088427845644) * 10 ^ 70 +
        0874904397009835605671741979120255607065940949300570958164367680048198) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 73 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 25 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_264 :
    recurrence2Scalar1Exceptional.coeff 264 =
      (((2609835216285974475213494431694238885732375411890731 * 10 ^ 70 +
        0471200142676432321745508364048189354647756327849444522502887147328961) * 10 ^ 70 +
        7033790217289110102391964754094376422693513488310959152267199517509135) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 74 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 24 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_265 :
    recurrence2Scalar1Exceptional.coeff 265 =
      (((506074841025927124709545345942944922280599429649027 * 10 ^ 70 +
        2690938939159366845314330719277905794751202530575606286125805854218406) * 10 ^ 70 +
        2895486023269091306616231849675119632967027706501291818999550128651815) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 75 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 23 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_266 :
    recurrence2Scalar1Exceptional.coeff 266 =
      -(((925876573057010616747879539194460290971502228091411 * 10 ^ 70 +
        4970470449422209861649798382042268302398169888735133200474582913550634) * 10 ^ 70 +
        1436414899841050831984530376721261737254680854819921033593811342199841) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 76 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 22 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_267 :
    recurrence2Scalar1Exceptional.coeff 267 =
      (((701493559685272532679419546164001717512905995648673 * 10 ^ 70 +
        3330874571606305914664170072575465668206346474768004852881627471404613) * 10 ^ 70 +
        1653523209480982345076402888794967427411805291224738092248980421926118) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 77 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 21 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_268 :
    recurrence2Scalar1Exceptional.coeff 268 =
      -(((420392789695734837937121543084914106025034377243729 * 10 ^ 70 +
        3373591932901044291550420819124519351677247563643322191984177011905895) * 10 ^ 70 +
        5462703869373757097036461461585922177694735007717898046056617646878616) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 78 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 20 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_269 :
    recurrence2Scalar1Exceptional.coeff 269 =
      (((217489051166540956434200245542125306565386301234374 * 10 ^ 70 +
        1564954825214605477877783069374355492765986810588100620129575396327911) * 10 ^ 70 +
        5307195499831414237635308906790127746360156004887265866045650811281518) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 79 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 19 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_270 :
    recurrence2Scalar1Exceptional.coeff 270 =
      -(((98340238504012480889138072060446228606955474883089 * 10 ^ 70 +
        1207059576356421402180198127500696158593518324563076335255993881943448) * 10 ^ 70 +
        9383685454063235023759918048009678037433551252352612317104513870848547) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 80 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 18 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_271 :
    recurrence2Scalar1Exceptional.coeff 271 =
      (((38120919228884517381483887267413530239741400782368 * 10 ^ 70 +
        7902288491408393706843070512945203622738767058402416643853647688665191) * 10 ^ 70 +
        0751195123110763813368175838129258432357050802013631436274960910709793) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 81 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 17 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_272 :
    recurrence2Scalar1Exceptional.coeff 272 =
      -(((11853476396326974167368984742918566015512152940519 * 10 ^ 70 +
        6633587589776093458109627919079218056000365628492707035537196881677914) * 10 ^ 70 +
        1553444472298813426075970097626769071721940778101932161760230548922902) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 82 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 16 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_273 :
    recurrence2Scalar1Exceptional.coeff 273 =
      (((2246123717209421677595866672675350867046007613228 * 10 ^ 70 +
        1030938953383516638387029245729719478720133814162502850452830070618341) * 10 ^ 70 +
        5939461245471744773296316662123744172986726057865048516030284647068849) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 83 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 15 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_274 :
    recurrence2Scalar1Exceptional.coeff 274 =
      (((422437618448613377321595837314087306773346995939 * 10 ^ 70 +
        0682160608346267723106785032818241761415237483587308506393902459011011) * 10 ^ 70 +
        8968880043987852480905239798987646126872209895773240145845482100566934) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 84 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 14 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_275 :
    recurrence2Scalar1Exceptional.coeff 275 =
      -(((736661539716578859351969249080114006081840022098 * 10 ^ 70 +
        8197525183376184462598772831620296519845275530461329350219152708751262) * 10 ^ 70 +
        2867223244460142042029593633242111786075536308945414036363026093157541) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 85 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 13 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_276 :
    recurrence2Scalar1Exceptional.coeff 276 =
      (((495312937619988782188096108823294971304005762111 * 10 ^ 70 +
        5472928583961738523125261233279865899583659349304722318982382340536825) * 10 ^ 70 +
        7790302119551478281905074512111323839903346046244874711973278601855578) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 86 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 12 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_277 :
    recurrence2Scalar1Exceptional.coeff 277 =
      -(((251484773881498340751675969719506462481496782784 * 10 ^ 70 +
        2194046633330013723800306063249257152217137920490442919933759645035438) * 10 ^ 70 +
        9025642328127356603616379718705341539905448285760499059514044609373616) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 87 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 11 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_278 :
    recurrence2Scalar1Exceptional.coeff 278 =
      (((105529917226001600547138826612528151578669662722 * 10 ^ 70 +
        6390554926976845993869576000072507893260012084502400596946027572727978) * 10 ^ 70 +
        1651754204576217878038096258430353660522425068429292041074781605573017) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 88 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 10 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_279 :
    recurrence2Scalar1Exceptional.coeff 279 =
      -(((35910999641676217974502284904659567333541544011 * 10 ^ 70 +
        0069105401002549266702096317055200999427290151687319666245875379543475) * 10 ^ 70 +
        6377280774951695859848117229823807655194028779581765654096590017205408) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 89 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 9 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_280 :
    recurrence2Scalar1Exceptional.coeff 280 =
      (((8245083674630212128765448772456800407214586203 * 10 ^ 70 +
        6354566928045829293115254330124750822659966720357585513900625048884804) * 10 ^ 70 +
        5880667301610533102133943514023403869198885163045339148063662892269320) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 90 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 8 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_281 :
    recurrence2Scalar1Exceptional.coeff 281 =
      (((411237471608906739216584211368111277811425248 * 10 ^ 70 +
        5490688562709363789719798109385394646075337992156678202392829878461877) * 10 ^ 70 +
        6995165646499885373428711554194698095466994388038430143880768495950203) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 91 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 7 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_282 :
    recurrence2Scalar1Exceptional.coeff 282 =
      -(((1906868444398349072812764040985052552133159958 * 10 ^ 70 +
        7533350731704272088390323892502069898668001958835782328711693553398869) * 10 ^ 70 +
        1467904947234030707098788627346584387508043443449854461502952616716747) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 92 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 6 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_283 :
    recurrence2Scalar1Exceptional.coeff 283 =
      (((1391629501884391733677362727907458227440171188 * 10 ^ 70 +
        1981705782641999906225827179237132531786263472384761375897361638305419) * 10 ^ 70 +
        9298880794650851540284265550220087532305615279265899973135255981899870) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 93 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 5 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_284 :
    recurrence2Scalar1Exceptional.coeff 284 =
      -(((697686086963904293807721636832923336195412453 * 10 ^ 70 +
        9667174981559504999009609620047534227760040254592347212257109260619468) * 10 ^ 70 +
        5989375074185782134455559792478906361416509873241889176830425089261275) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 94 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 4 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
