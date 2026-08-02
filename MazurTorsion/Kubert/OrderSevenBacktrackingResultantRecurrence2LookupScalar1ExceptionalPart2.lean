/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence2Scalar1Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (377 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_377 :
    recurrence2Scalar1Exceptional.coeff 377 =
      (-22184513883895966463809066886094923303728247975974439 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 187 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 7 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (378 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_378 :
    recurrence2Scalar1Exceptional.coeff 378 =
      (-53708855041652292668627997828384097665840127929 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 188 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 6 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (379 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_379 :
    recurrence2Scalar1Exceptional.coeff 379 =
      (-50097319764383513268107953371483652738857 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 189 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 5 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (380 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_380 :
    recurrence2Scalar1Exceptional.coeff 380 =
      (-6849243402748311740365115398043142 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 381 = 190 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 4 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (381 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_381 :
    recurrence2Scalar1Exceptional.coeff 381 =
      (-40066926400541939420063298 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 382 = 191 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 3 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (382 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_382 :
    recurrence2Scalar1Exceptional.coeff 382 =
      (-76255717385539356 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 383 = 192 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 2 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (383 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_383 :
    recurrence2Scalar1Exceptional.coeff 383 =
      (-47165519 : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 384 = 193 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 1 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
