/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Exceptional coefficient convolution

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
  recurrence2C3_coeff_0
  recurrence2C3_coeff_1
  recurrence2C3_coeff_2
  recurrence2C3_coeff_3
  recurrence2C3_coeff_4
  recurrence2C3_coeff_5
  recurrence2C3_coeff_6
  recurrence2C3_coeff_7
  recurrence2C3_coeff_8
  recurrence2C3_coeff_9
  recurrence2C3_coeff_10
  recurrence2C3_coeff_11
  recurrence2C3_coeff_12
  recurrence2C3_coeff_13
  recurrence2C3_coeff_14
  recurrence2C3_coeff_15
  recurrence2C3_coeff_16
  recurrence2C3_coeff_17
  recurrence2C3_coeff_18
  recurrence2C3_coeff_19
  recurrence2C3_coeff_20
  recurrence2C3_coeff_21
  recurrence2C3_coeff_22
  recurrence2C3_coeff_23
  recurrence2C3_coeff_24
  recurrence2C3_coeff_25
  recurrence2C3_coeff_26
  recurrence2C3_coeff_27
  recurrence2C3_coeff_28
  recurrence2C3_coeff_29
  recurrence2C3_coeff_30
  recurrence2C3_coeff_31
  recurrence2C3_coeff_32
  recurrence2C3_coeff_33
  recurrence2C3_coeff_34
  recurrence2C3_coeff_35
  recurrence2C3_coeff_36
  recurrence2C3_coeff_37
  recurrence2C3_coeff_38
  recurrence2C3_coeff_39
  recurrence2C3_coeff_40
  recurrence2C3_coeff_41
  recurrence2C3_coeff_42
  recurrence2C3_coeff_43
  recurrence2C3_coeff_44
  recurrence2C3_coeff_45
  recurrence2C3_coeff_46
  recurrence2C3_coeff_47
  recurrence2C3_coeff_48
  recurrence2C3_coeff_49
  recurrence2C3_coeff_50
  recurrence2C3_coeff_51
  recurrence2C3_coeff_52
  recurrence2C3_coeff_53
  recurrence2C3_coeff_54
  recurrence2C3_coeff_55
  recurrence2C3_coeff_56
  recurrence2C3_coeff_57
  recurrence2C3_coeff_58
  recurrence2C3_coeff_59
  recurrence2C3_coeff_60
  recurrence2C3_coeff_61
  recurrence2C3_coeff_62
  recurrence2C3_coeff_63
  recurrence2C3_coeff_64
  recurrence2C3_coeff_65
  recurrence2C3_coeff_66
  recurrence2C3_coeff_67
  recurrence2C3_coeff_68
  recurrence2C3_coeff_69
  recurrence2C3_coeff_70
  recurrence2C3_coeff_71
  recurrence2C3_coeff_72
  recurrence2C3_coeff_73
  recurrence2C3_coeff_74
  recurrence2C3_coeff_75
  recurrence2C3_coeff_76
  recurrence2C3_coeff_77
  recurrence2C3_coeff_78
  recurrence2C3_coeff_79
  recurrence2C3_coeff_80
  recurrence2C3_coeff_81
  recurrence2C3_coeff_82
  recurrence2C3_coeff_83
  recurrence2C3_coeff_84
  recurrence2C3_coeff_85
  recurrence2C3_coeff_86
  recurrence2C3_coeff_87
  recurrence2C3_coeff_88
  recurrence2C3_coeff_89
  recurrence2C3_coeff_90
  recurrence2C3_coeff_91
  recurrence2C3_coeff_92
  recurrence2C3_coeff_93
  recurrence2C3_coeff_94
  recurrence2C3_coeff_95
  recurrence2C3_coeff_96
  recurrence2C3_coeff_97
  recurrence2C3_coeff_98
  recurrence2C3_coeff_99
  recurrence2C3_coeff_100
  recurrence2C3_coeff_101
  recurrence2C3_coeff_102
  recurrence2C3_coeff_103
  recurrence2C3_coeff_104
  recurrence2C3_coeff_105
  recurrence2C3_coeff_106
  recurrence2C3_coeff_107
  recurrence2C3_coeff_108
  recurrence2C3_coeff_109
  recurrence2C3_coeff_110
  recurrence2C3_coeff_111
  recurrence2C3_coeff_112
  recurrence2C3_coeff_113
  recurrence2C3_coeff_114
  recurrence2C3_coeff_115
  recurrence2C3_coeff_116
  recurrence2C3_coeff_117
  recurrence2C3_coeff_118
  recurrence2C3_coeff_119
  recurrence2C3_coeff_120
  recurrence2C3_coeff_121
  recurrence2C3_coeff_122
  recurrence2C3_coeff_123
  recurrence2C3_coeff_124
  recurrence2C3_coeff_125
  recurrence2C3_coeff_126
  recurrence2C3_coeff_127
  recurrence2C3_coeff_128
  recurrence2C3_coeff_129
  recurrence2C3_coeff_130
  recurrence2C3_coeff_131
  recurrence2C3_coeff_132
  recurrence2C3_coeff_133
  recurrence2C3_coeff_134
  recurrence2C3_coeff_135
  recurrence2C3_coeff_136
  recurrence2C3_coeff_137
  recurrence2C3_coeff_138
  recurrence2C3_coeff_139
  recurrence2C3_coeff_140
  recurrence2C3_coeff_141
  recurrence2C3_coeff_142
  recurrence2C3_coeff_143
  recurrence2C3_coeff_144
  recurrence2C3_coeff_145
  recurrence2C3_coeff_146
  recurrence2C3_coeff_147
  recurrence2C3_coeff_148
  recurrence2C3_coeff_149
  recurrence2C3_coeff_150
  recurrence2C3_coeff_151
  recurrence2C3_coeff_152
  recurrence2C3_coeff_153
  recurrence2C3_coeff_154
  recurrence2C3_coeff_155
  recurrence2C3_coeff_156
  recurrence2C3_coeff_157
  recurrence2C3_coeff_158
  recurrence2C3_coeff_159
  recurrence2C3_coeff_160
  recurrence2C3_coeff_161
  recurrence2C3_coeff_162
  recurrence2C3_coeff_163
  recurrence2C3_coeff_164
  recurrence2C3_coeff_165
  recurrence2C3_coeff_166
  recurrence2C3_coeff_167
  recurrence2C3_coeff_168
  recurrence2C3_coeff_169
  recurrence2C3_coeff_170
  recurrence2C3_coeff_171
  recurrence2C3_coeff_172
  recurrence2C3_coeff_173
  recurrence2C3_coeff_174
  recurrence2C3_coeff_175
  recurrence2C3_coeff_176
  recurrence2C3_coeff_177
  recurrence2C3_coeff_178
  recurrence2C3_coeff_179
  recurrence2C3_coeff_180
  recurrence2C3_coeff_181
  recurrence2C3_coeff_182

private theorem recurrence2Scalar3Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_298 :
    recurrence2Scalar3Exceptional.coeff 298 =
      (((31315577765430492339634964709895512 * 10 ^ 70 +
        5305895887242262174363910871568862353317474191942257154149170609826113) * 10 ^ 70 +
        5971908394369747430654120919693740555761283613917222447613564224955932) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 116 +
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
  rw [recurrence2Scalar3Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_299 :
    recurrence2Scalar3Exceptional.coeff 299 =
      -(((1185903059780953569901756633584901 * 10 ^ 70 +
        2311035943667069335254098287213696746007323598647968792580978742292894) * 10 ^ 70 +
        0727893618076353141400665215435977038152610378601925194640885973219262) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 117 +
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
  rw [recurrence2Scalar3Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_300 :
    recurrence2Scalar3Exceptional.coeff 300 =
      -(((1719899521203314074502581195242152 * 10 ^ 70 +
        8247232041497803169185226719333414093365442539546180297900456385337281) * 10 ^ 70 +
        6431068998672147467136872174278463030532678302032370610159114002080338) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 118 +
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
  rw [recurrence2Scalar3Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_301 :
    recurrence2Scalar3Exceptional.coeff 301 =
      (((735968159483126522632950018325020 * 10 ^ 70 +
        2802152539723580275979510791111827327941692842486315723919197625020974) * 10 ^ 70 +
        4359829805983645967125494325550724352219255335495765588994166258658899) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 119 +
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
  rw [recurrence2Scalar3Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_302 :
    recurrence2Scalar3Exceptional.coeff 302 =
      -(((163041603536041863668420892897848 * 10 ^ 70 +
        8750391088384324459158776596462001669707935170211857900444877895631794) * 10 ^ 70 +
        8015219190794478996970277629605490507139361013392544883502277139054307) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 120 +
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
  rw [recurrence2Scalar3Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_303 :
    recurrence2Scalar3Exceptional.coeff 303 =
      (((14184689242642976213465136103448 * 10 ^ 70 +
        2655044401629101371544675717749331377823933029794934377649642404370727) * 10 ^ 70 +
        4549148635124437419539300132425442308814900002110507435378306232907487) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 121 +
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
  rw [recurrence2Scalar3Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_304 :
    recurrence2Scalar3Exceptional.coeff 304 =
      (((4240815240078593535913241483891 * 10 ^ 70 +
        8602570452210476320520687066831231716603477060983501927672993918149863) * 10 ^ 70 +
        3488489965847033183518095239313504184269613063670114960996311172206598) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 122 +
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
  rw [recurrence2Scalar3Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_305 :
    recurrence2Scalar3Exceptional.coeff 305 =
      -(((2111577665767913287536644415335 * 10 ^ 70 +
        6259910847332565788607490913840794814442454511955875977097335796976617) * 10 ^ 70 +
        9797155314946012278669575609705547261150439691734117903745553736517020) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 123 +
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
  rw [recurrence2Scalar3Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_306 :
    recurrence2Scalar3Exceptional.coeff 306 =
      (((445098831818119039400159794321 * 10 ^ 70 +
        5342221196331431618330785515068329228040642097477958489755285198327349) * 10 ^ 70 +
        3620559671775593643792344631601327253423914961557788444176854525658253) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 124 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 6 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_307 :
    recurrence2Scalar3Exceptional.coeff 307 =
      -(((34122751958129011253211351454 * 10 ^ 70 +
        0317697398825117808837412420428882614045746895800205642762462585867851) * 10 ^ 70 +
        3020879275344514031138815647433577264517546094166416910399344896549896) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 125 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 5 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_308 :
    recurrence2Scalar3Exceptional.coeff 308 =
      -(((9656759258236155650610026104 * 10 ^ 70 +
        9550342196359538609139415559273389294333583513743836586829061157120948) * 10 ^ 70 +
        1313390071485300064040373801723919761866072243699781071110014524631354) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 126 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 4 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_309 :
    recurrence2Scalar3Exceptional.coeff 309 =
      (((3975307792740728796062104907 * 10 ^ 70 +
        8911055577250854567912517849661110761761117237376926845904453342461201) * 10 ^ 70 +
        9565104480752980642484910444530628090604490499573840892779222876650053) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 127 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 3 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_310 :
    recurrence2Scalar3Exceptional.coeff 310 =
      -(((645707799401380989676394836 * 10 ^ 70 +
        0331245126783241378487650867251932925236686565848078535449564513388835) * 10 ^ 70 +
        1901590969254104980871113103954885909583851403380782732957131345152687) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 128 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 2 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_311 :
    recurrence2Scalar3Exceptional.coeff 311 =
      (((14502847665268101387809272 * 10 ^ 70 +
        5501990490342498164323296299942521742615899583016664061640981735004721) * 10 ^ 70 +
        1810307207736641251975325029499616293723051506601782633754942300597605) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 129 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 1 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_312 :
    recurrence2Scalar3Exceptional.coeff 312 =
      (((18184661988017653898494843 * 10 ^ 70 +
        8613778291820083932596806924329965526437211536504918297664867897639226) * 10 ^ 70 +
        1958163218453368924984922409396098642738317836315494058319433441783838) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 130 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_313 :
    recurrence2Scalar3Exceptional.coeff 313 =
      -(((4378586020902044179471843 * 10 ^ 70 +
        9490096588277390213824596965455508096808332910919258725213534458842239) * 10 ^ 70 +
        1881940969542920918603797718781696741974211779534301299812843269761747) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 131 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 31 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (314 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_314 :
    recurrence2Scalar3Exceptional.coeff 314 =
      (((362619573673863331335265 * 10 ^ 70 +
        1507165753536465208158680072908473150092304424851868184497981298071994) * 10 ^ 70 +
        9711383654634158251854071515459919326095961092683140858958104967405130) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 132 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 30 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (315 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_315 :
    recurrence2Scalar3Exceptional.coeff 315 =
      (((49290144641088923002317 * 10 ^ 70 +
        4307264165334683868367147405623524549089738291939809016648165011997344) * 10 ^ 70 +
        2270772995009613533691330986927775422556948302481005837676504386548349) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 133 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 29 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (316 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_316 :
    recurrence2Scalar3Exceptional.coeff 316 =
      -(((17972815460320302398830 * 10 ^ 70 +
        7201270876283223463985522936742761021589399493312204103830318999502028) * 10 ^ 70 +
        0490277262220974835911443988535902160055498934682360749413270098185717) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 134 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 28 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (317 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_317 :
    recurrence2Scalar3Exceptional.coeff 317 =
      (((1846192571141687709395 * 10 ^ 70 +
        1628142404251798606078260433917584214221896695745326509686113320965347) * 10 ^ 70 +
        5504274470602472747421182559727232440487058854845645523981821905256466) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 135 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 27 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (318 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_318 :
    recurrence2Scalar3Exceptional.coeff 318 =
      (((105217693871032964878 * 10 ^ 70 +
        4343291077767357578921994351101980298935311728805943554642580494281449) * 10 ^ 70 +
        2579650605745543830129376988477494274631206988464049927833572737200113) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 136 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 26 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (319 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_319 :
    recurrence2Scalar3Exceptional.coeff 319 =
      -(((52514457794853290416 * 10 ^ 70 +
        5690824183415309777551650563533578910992749609701361562124215025429664) * 10 ^ 70 +
        7677866030679165625458504762245581442489869681633870932461470957402999) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 137 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 25 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (320 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_320 :
    recurrence2Scalar3Exceptional.coeff 320 =
      (((4983945515923579229 * 10 ^ 70 +
        0862375241597179048679256610190390142209320228827177370925624002710070) * 10 ^ 70 +
        5191066461964921057440980736841105309476027641000634627277023596954814) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 138 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 24 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (321 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_321 :
    recurrence2Scalar3Exceptional.coeff 321 =
      (((307256225893155883 * 10 ^ 70 +
        4339558456223457008293003331039840957859431612416880795288701792919841) * 10 ^ 70 +
        4525390640605082703863430630371116653361627883034567346393868310261731) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 139 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 23 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (322 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_322 :
    recurrence2Scalar3Exceptional.coeff 322 =
      -(((113881808366572830 * 10 ^ 70 +
        0848762813201843720913207334131739596600313482194118891211751463527242) * 10 ^ 70 +
        6754060209857795452302758799349515878436327235573030261151847263433037) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 140 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 22 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (323 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_323 :
    recurrence2Scalar3Exceptional.coeff 323 =
      (((6783009172846291 * 10 ^ 70 +
        0521927382188234268731617686945411531947630247697344723155338264319742) * 10 ^ 70 +
        7082044862210872841113014936336864339078290235751344947728864963873024) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 141 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 21 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (324 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_324 :
    recurrence2Scalar3Exceptional.coeff 324 =
      (((950493797488273 * 10 ^ 70 +
        1680405628816914502065651633802378815499165154277234461219159785009573) * 10 ^ 70 +
        4818284782856685368733500511536231436051736526045108019901536833249656) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 142 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 20 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (325 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_325 :
    recurrence2Scalar3Exceptional.coeff 325 =
      -(((159553747124672 * 10 ^ 70 +
        7148724192475715856426775679824788019820645523470395442368302027852075) * 10 ^ 70 +
        7834020336149988247225397964913104105148682804693327462867469560890174) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 143 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 19 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (326 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_326 :
    recurrence2Scalar3Exceptional.coeff 326 =
      -(((86134860872 * 10 ^ 70 +
        1339483130024800522459015620311354435507012563578773157231323000103778) * 10 ^ 70 +
        9959357559256514013362679521439080558039890604690018039764965443837350) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 144 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 18 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (327 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_327 :
    recurrence2Scalar3Exceptional.coeff 327 =
      (((1687765405172 * 10 ^ 70 +
        5866470758904406523602237001817458533165477117702557383714785895166664) * 10 ^ 70 +
        1163150633211544428134261140346556663231218330722698631934513025985028) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 145 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 17 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (328 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_328 :
    recurrence2Scalar3Exceptional.coeff 328 =
      -(((79957426489 * 10 ^ 70 +
        2636583478019509936644912257291340431109612335454349411054630783103409) * 10 ^ 70 +
        3617118709401598176800721322906115303851293235469250581172180603268526) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 146 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 16 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (329 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_329 :
    recurrence2Scalar3Exceptional.coeff 329 =
      -(((11811454326 * 10 ^ 70 +
        4457873891767390240807604083779642538869883044450231328768604782932895) * 10 ^ 70 +
        3317009058138894399378952416457986625433897863774985305744478653814935) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 147 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 15 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (330 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_330 :
    recurrence2Scalar3Exceptional.coeff 330 =
      (((975085711 * 10 ^ 70 +
        2394795276943653692654001118765087564938764393525526095035721195333643) * 10 ^ 70 +
        9979243808698867611047024160143910739148382363099348141156497710074744) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 148 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 14 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (331 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_331 :
    recurrence2Scalar3Exceptional.coeff 331 =
      (((67644858 * 10 ^ 70 +
        3163081864546963331209946989254349111114006392657307278649747774003544) * 10 ^ 70 +
        6760216104949666079701871229754740943167472899000250390737141804205975) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 149 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 13 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (332 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_332 :
    recurrence2Scalar3Exceptional.coeff 332 =
      -(((7064388 * 10 ^ 70 +
        5360024405033725036406087625548567429334154600564038263164130927070977) * 10 ^ 70 +
        3875066791003954831804793525881259906275109672501453547537289340876325) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 150 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 12 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (333 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_333 :
    recurrence2Scalar3Exceptional.coeff 333 =
      -(((402242 * 10 ^ 70 +
        9327336412219542433261022659559125416985014792343469526329647631502876) * 10 ^ 70 +
        6737602674406546623225052612040906739817029279480051766178498150270642) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 151 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 11 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (334 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_334 :
    recurrence2Scalar3Exceptional.coeff 334 =
      (((34343 * 10 ^ 70 +
        0980348928803532061703556069385295805641469758444913920697881048490045) * 10 ^ 70 +
        7301723371428184219188717541650602811904115041496564334056894310179547) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 152 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 10 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
