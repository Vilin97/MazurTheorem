/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart0Simp
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

private theorem recurrence2Scalar0Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (202 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_202 :
    recurrence2Scalar0Exceptional.coeff 202 =
      (((150211037053515005866686789572907271197734774145889908877309 * 10 ^ 70 +
        6067283640854920927814285134857253219047620933163873953882235515684550) * 10 ^ 70 +
        6663531107760849853738313008612171060211127689202691516749730243636838) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 8 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 26 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (203 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_203 :
    recurrence2Scalar0Exceptional.coeff 203 =
      (((338280106289080721035084990983695272312165743056341319016107 * 10 ^ 70 +
        9374085253821088887061692785049606667616338787246876102856348638977690) * 10 ^ 70 +
        9891094984008748113658023275499196499505259901698050907420958323389209) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 9 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 25 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (204 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_204 :
    recurrence2Scalar0Exceptional.coeff 204 =
      -(((1258276071591303393091562471786249170596540666175555633697728 * 10 ^ 70 +
        0445131635680308459177358386932115243462189706295167571778387695032261) * 10 ^ 70 +
        3474263878495999685925163186240793790206339762637163709015045626416278) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 10 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 24 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (205 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_205 :
    recurrence2Scalar0Exceptional.coeff 205 =
      (((2721700621788597938699146415772158302930101530984316911497090 * 10 ^ 70 +
        6600657047747095019999108177086511677468352581743699331717184028777494) * 10 ^ 70 +
        3159473487331556053454116001407931194746128256879048281090939289655029) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 11 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 23 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (206 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_206 :
    recurrence2Scalar0Exceptional.coeff 206 =
      -(((4772196004439972827083676986064704291497917756535328079976841 * 10 ^ 70 +
        4801850662844964361923319270623685890235310434461573121163461925988900) * 10 ^ 70 +
        2512492968725345444811356420869038184665382451711265087103256279686140) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 12 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 22 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (207 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_207 :
    recurrence2Scalar0Exceptional.coeff 207 =
      (((7333666464322236419890386107666122440816100906357099055061641 * 10 ^ 70 +
        8490162450464746563445196037588669692165093377968212211253814267906241) * 10 ^ 70 +
        4480683860511938690025285729497563014787185460901150331825271491109113) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 13 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 21 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (208 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_208 :
    recurrence2Scalar0Exceptional.coeff 208 =
      -(((10168804932192964914600792097624077449761942563090455355861574 * 10 ^ 70 +
        2688860095596308695798817314380479312464680675248007519131450941152072) * 10 ^ 70 +
        7060056293219033584814947637485101492583133737881984203252990535943062) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 14 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 20 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (209 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_209 :
    recurrence2Scalar0Exceptional.coeff 209 =
      (((12865833547226446978342207310670026985605484211792088439294697 * 10 ^ 70 +
        3265221316599214494976524768821755989181589325788000796813762938875046) * 10 ^ 70 +
        3439517821346597179074706407133865400368958324892563145328095361842891) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 15 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 19 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (210 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_210 :
    recurrence2Scalar0Exceptional.coeff 210 =
      -(((14869585113370496904553417880793369281935377778477098422657499 * 10 ^ 70 +
        8990795310667970237693483817886622261255794292956424975229657200085836) * 10 ^ 70 +
        9191526648224636722091136798872943221035779765249836690402848528156293) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 16 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 18 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (211 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_211 :
    recurrence2Scalar0Exceptional.coeff 211 =
      (((15564118718280025159733804075402176728890067363279623315889566 * 10 ^ 70 +
        3348916377778286525640306742353946780070841723596133375879944119145521) * 10 ^ 70 +
        1506158376546654248994619304222311987132484516976429723492123474704761) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 17 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 17 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (212 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_212 :
    recurrence2Scalar0Exceptional.coeff 212 =
      -(((14399359342926112338734322463924749063679470495696690873151655 * 10 ^ 70 +
        1716723629197480999417979514619820572303458391757979581592414194153176) * 10 ^ 70 +
        0050771242675485667393487170917267494878485273078108987349643473257150) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 18 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 16 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (213 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_213 :
    recurrence2Scalar0Exceptional.coeff 213 =
      (((11037591882442759029571413378658321006068931175396068783655023 * 10 ^ 70 +
        6045776908699197573231286316789047567667304551017378664838561498008149) * 10 ^ 70 +
        2961665101982923898473603155057408769734336518538553418159471396480428) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 19 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 15 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (214 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_214 :
    recurrence2Scalar0Exceptional.coeff 214 =
      -(((5482770459869292485143739258738756590403928524028939800694353 * 10 ^ 70 +
        6248242534636432338644416772775085432357170524972057797192260002336972) * 10 ^ 70 +
        5279285076645726013621160215724398317038911587277743669100773000316174) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 20 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 14 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (215 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_215 :
    recurrence2Scalar0Exceptional.coeff 215 =
      -(((1847735077419142560328944731150137797044933874215543869545587 * 10 ^ 70 +
        7928298767793473825192347833805835196695197807015902254045841422352691) * 10 ^ 70 +
        4921456549060924526304463859553260939279190472123760585749821797082008) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 21 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 13 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (216 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_216 :
    recurrence2Scalar0Exceptional.coeff 216 =
      (((10139828830281751455799044316201770566085831454281864434757218 * 10 ^ 70 +
        8867067522639561153784020094708853461200641018944715945193814907710724) * 10 ^ 70 +
        6104968474063146243899221570966727537505532969331525231904773359258391) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 22 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 12 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (217 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_217 :
    recurrence2Scalar0Exceptional.coeff 217 =
      -(((18297334041591478485828378460392837335310209860522250225495095 * 10 ^ 70 +
        1903551966078571938509290401094386481548889998456635933013438800106717) * 10 ^ 70 +
        3892307330508313890895103851752428615860276014605835870764382113265477) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 23 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 11 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (218 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_218 :
    recurrence2Scalar0Exceptional.coeff 218 =
      (((25136571652895232199479382001406774477509081076118389684353881 * 10 ^ 70 +
        6357838544395964522698843545318605241837769028801816545176174394421887) * 10 ^ 70 +
        5512600950693716658372728865006575417868411141586794962726231021253107) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 24 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 10 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (219 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_219 :
    recurrence2Scalar0Exceptional.coeff 219 =
      -(((29617865857484730695189788489365383558755936786482402472691407 * 10 ^ 70 +
        0676623569086336029964889178093786957283793322732773623027623221677195) * 10 ^ 70 +
        5338741114595098451027913299003160593139190880480279565536644343952870) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 25 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 9 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (220 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_220 :
    recurrence2Scalar0Exceptional.coeff 220 =
      (((31057280420131563954689397853419648318000957054499590093567580 * 10 ^ 70 +
        6788702736956598199795510368160889616617616941631135729243656965055365) * 10 ^ 70 +
        3480288095486253466500215649465706458925648456993315337486776978930139) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 26 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 8 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (221 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_221 :
    recurrence2Scalar0Exceptional.coeff 221 =
      -(((29264823848185510524694667716653219724448263501303100318146064 * 10 ^ 70 +
        3512080218502920245302863294817543152279157598331067876052892500736907) * 10 ^ 70 +
        0641352593342261647935677142361749058379511743573314781225452704248369) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 27 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 7 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (222 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_222 :
    recurrence2Scalar0Exceptional.coeff 222 =
      (((24574591862221308463544605230433207131128672731139531066142593 * 10 ^ 70 +
        4967247200461754910095069655216050943347499283638443985808981222732822) * 10 ^ 70 +
        9377690592897754606587816968779994673593820335597250229119122732893409) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 28 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 6 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (223 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_223 :
    recurrence2Scalar0Exceptional.coeff 223 =
      -(((17761789011457390635812827428632125187708307326067469728745758 * 10 ^ 70 +
        5149574552253705184998246269854203405141088970990691697223346299866098) * 10 ^ 70 +
        4290068731422447187910511925373513225411044336597592100393609556880438) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 29 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 5 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (224 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_224 :
    recurrence2Scalar0Exceptional.coeff 224 =
      (((9871723272554640833651506666893481653275996879745488177471553 * 10 ^ 70 +
        0422149688202050131409925341283658192243765392779505720899857078320931) * 10 ^ 70 +
        9540629343595378768597982915257352669486532195667815016658603012018564) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 30 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 4 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (225 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_225 :
    recurrence2Scalar0Exceptional.coeff 225 =
      -(((2007200185082239778052784099328348245048073127595446625492546 * 10 ^ 70 +
        1115192038477087045746145218101840411334979530595644446254239982243456) * 10 ^ 70 +
        3274380669841805842757944953012410043272137151880572861742080636490009) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 31 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 3 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (226 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_226 :
    recurrence2Scalar0Exceptional.coeff 226 =
      -(((4872740344210219156775554040303882890544744884912235550920086 * 10 ^ 70 +
        4428233533483716798542052103918086564413582197330139308968113280961268) * 10 ^ 70 +
        0904314708635256732940845925092003428729548146012896799209703564242857) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 32 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 2 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (227 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_227 :
    recurrence2Scalar0Exceptional.coeff 227 =
      (((10098702311303332077132345247025058520224630351295563264034954 * 10 ^ 70 +
        2218675517356268077206286864066679078787073464818383137109710261455142) * 10 ^ 70 +
        9010270847726673068472251033907704965246469551877825043468676345807083) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 33 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 1 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (228 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_228 :
    recurrence2Scalar0Exceptional.coeff 228 =
      -(((13357210468704475567906971447528491556618115238311835743550688 * 10 ^ 70 +
        2153479195989488111695140219057789412275587518852230815721377262598036) * 10 ^ 70 +
        4380292215649121283866082118868529551460457300917978196687709271482571) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 34 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (229 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_229 :
    recurrence2Scalar0Exceptional.coeff 229 =
      (((14676503562216115304843292338979624892060828945243149721927725 * 10 ^ 70 +
        0231398816600271906332878043314780439703516919894405525020760678194187) * 10 ^ 70 +
        0483790862385955579868956648909041791648742344416914240229586011811790) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 35 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 31 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (230 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_230 :
    recurrence2Scalar0Exceptional.coeff 230 =
      -(((14350426922119973449542293717859184644685064507710343740245509 * 10 ^ 70 +
        9389032531942351473804077924297617268916672954250607983992931197520125) * 10 ^ 70 +
        4170013058987901093523246953040748832049329091193135422031359386109976) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 36 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 30 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (231 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_231 :
    recurrence2Scalar0Exceptional.coeff 231 =
      (((12829753817066062790602502516976764751262198533336402516977852 * 10 ^ 70 +
        0858334498543355773919842427238147197976727277850202997937569529394131) * 10 ^ 70 +
        2129017125967802822327229146043940275414802913654716360888968050079435) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 37 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 29 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
