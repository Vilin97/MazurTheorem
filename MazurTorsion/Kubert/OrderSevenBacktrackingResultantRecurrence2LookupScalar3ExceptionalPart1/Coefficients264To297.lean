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

private theorem recurrence2Scalar3Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_264 :
    recurrence2Scalar3Exceptional.coeff 264 =
      -(((18288676639309147657558967271986523619781007840973 * 10 ^ 70 +
        9609976933850125541705463579406388892042510971585824292034562759112770) * 10 ^ 70 +
        4621099211061975354852105415603197558921457308702620138148101042550522) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 82 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_265 :
    recurrence2Scalar3Exceptional.coeff 265 =
      (((6223882649547690311918378706681390230968962328174 * 10 ^ 70 +
        4806774624869061416262765954378961709030337539251232401180556654842809) * 10 ^ 70 +
        1918324852065327189457344073607600159473857991101860946394901096903321) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 83 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_266 :
    recurrence2Scalar3Exceptional.coeff 266 =
      -(((1789819969922247298185363440242654929756032779241 * 10 ^ 70 +
        0803705517028096071971730292220675176730085565617402874099242259908208) * 10 ^ 70 +
        3735601165254000141231825919771292706155340040599479914576107120798657) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 84 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 14 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_267 :
    recurrence2Scalar3Exceptional.coeff 267 =
      (((425498575780203037390851819410938976517934059135 * 10 ^ 70 +
        3534246052733328127413824746862600674778709536130394304007574102548711) * 10 ^ 70 +
        1084902440268325193964048229922210507099700973611108927186021250106680) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 85 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 13 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_268 :
    recurrence2Scalar3Exceptional.coeff 268 =
      -(((80938280138793195116189490832060853757136367630 * 10 ^ 70 +
        0209365456726378577921431510389466742908660079579082790211141053263331) * 10 ^ 70 +
        7424987567748008045993806304907058085667113201047716617245646730753306) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 86 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_269 :
    recurrence2Scalar3Exceptional.coeff 269 =
      (((12726458008400655442344340980933395539358485597 * 10 ^ 70 +
        3180314695696913682712392937193436691934188858598269450429429698341685) * 10 ^ 70 +
        6443563506996995435598941708610670618160699444902540545076838963301266) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 87 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 11 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_270 :
    recurrence2Scalar3Exceptional.coeff 270 =
      -(((2281889332628833386365871253442439942372019606 * 10 ^ 70 +
        0894615302880964158409220875061736327168984917488086859836400263341492) * 10 ^ 70 +
        5441788046941236874835641266506859965826992430658717365805100405366152) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 88 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 10 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_271 :
    recurrence2Scalar3Exceptional.coeff 271 =
      (((205464026878101052462435063116122542438888684 * 10 ^ 70 +
        0092641547209720423266810049970912891714444960275979320067969335970407) * 10 ^ 70 +
        2657205206330663379127590295429789863576614710293696602605127062532514) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 89 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 9 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_272 :
    recurrence2Scalar3Exceptional.coeff 272 =
      (((765778595882456889491225259340095600716281804 * 10 ^ 70 +
        9463457987544010565834453307722423805575095968527122463385541772775151) * 10 ^ 70 +
        7982531435802646166643607295079778308723131626386402032398164423926724) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 90 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 8 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_273 :
    recurrence2Scalar3Exceptional.coeff 273 =
      -(((1037313226967227244787424967394511622822380443 * 10 ^ 70 +
        3190726538362232238693488403853871137286469099167600670904042744059202) * 10 ^ 70 +
        6744762694984238383135571409860705665127939353155273499255320175773307) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 91 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 7 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_274 :
    recurrence2Scalar3Exceptional.coeff 274 =
      (((829624270278740067483357722349554127294010531 * 10 ^ 70 +
        4013191346762903010005652508724089814074169191371851099347842030762059) * 10 ^ 70 +
        9101800068790262537996523714441944924187260272074726393865891515047541) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 92 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 6 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_275 :
    recurrence2Scalar3Exceptional.coeff 275 =
      -(((488771774650832135479752482782326191137504936 * 10 ^ 70 +
        9294912450384944184547358375002138520898440183448189041657979727428478) * 10 ^ 70 +
        0259424685121931027881204763791559627102611968619931296255537933646348) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 93 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 5 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_276 :
    recurrence2Scalar3Exceptional.coeff 276 =
      (((221007978730176244356985708403843128497532455 * 10 ^ 70 +
        3922605904288521932133693936008129974022717139866864194062706338830908) * 10 ^ 70 +
        2412616517513103311817128200534217497819534029247549752004503884415947) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 94 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 4 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_277 :
    recurrence2Scalar3Exceptional.coeff 277 =
      -(((71812207135649821231708465867188579102377734 * 10 ^ 70 +
        6329208613496939192346374480085930653088072779681383876353138994250486) * 10 ^ 70 +
        9897796404706476418834976334340311829373730615955263866340346550612432) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 95 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 3 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_278 :
    recurrence2Scalar3Exceptional.coeff 278 =
      (((9942033438979607047569627113926039729096920 * 10 ^ 70 +
        1717209383262077677277789618582994076193096575714162313503141712840627) * 10 ^ 70 +
        3405934530724143885149701279042804168369503599301051409487363409745138) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 96 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 2 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_279 :
    recurrence2Scalar3Exceptional.coeff 279 =
      (((6922814771216284549987438387483208803299525 * 10 ^ 70 +
        3405061619646909019814625406347511961194155019724987140296682356541793) * 10 ^ 70 +
        3148171140358526744820355107685640341349709885779663253333721100065144) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 97 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 1 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_280 :
    recurrence2Scalar3Exceptional.coeff 280 =
      -(((7125616222550667644531956783990812739285531 * 10 ^ 70 +
        4688377822185049039984732682321358269927594053661154484139187576729023) * 10 ^ 70 +
        3821380064996593647602832011091057689222400039566818096144518708232515) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 98 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_281 :
    recurrence2Scalar3Exceptional.coeff 281 =
      (((3921165518767038915491479337616569328567981 * 10 ^ 70 +
        6330391657436555182251475409237581025299304086809053878070849103561074) * 10 ^ 70 +
        1884617611607607971583183792552114592594918256972941430085386560854794) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 99 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 31 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_282 :
    recurrence2Scalar3Exceptional.coeff 282 =
      -(((1524069763043601208447732237665755822368673 * 10 ^ 70 +
        6996157579695054395182672688805779559640711939266008502072929444937518) * 10 ^ 70 +
        7405192527954735069128932282080870425683259898451955854975228933647204) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 100 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 30 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_283 :
    recurrence2Scalar3Exceptional.coeff 283 =
      (((389153140583808574683453532661067536261312 * 10 ^ 70 +
        6052248643289635479976707494644445320043502324479256510485238511132797) * 10 ^ 70 +
        4380685984971439587775146871920931637757527318583719178636470144997510) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 101 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 29 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_284 :
    recurrence2Scalar3Exceptional.coeff 284 =
      -(((14330568683557188646310729530922269189635 * 10 ^ 70 +
        3377842285798941712754332238935333999274502921413884943928992498249785) * 10 ^ 70 +
        1702164162399598718377418250943443054518743766518893773383038288426859) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 102 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 28 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_285 :
    recurrence2Scalar3Exceptional.coeff 285 =
      -(((51385667559515234753821031435947196549660 * 10 ^ 70 +
        5891030632412504913709687739951582772709132656630930155691965193905765) * 10 ^ 70 +
        4555990904292845733478115327523221005943728163129527867823330532930221) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 103 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 27 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_286 :
    recurrence2Scalar3Exceptional.coeff 286 =
      (((35138617151578258091198490639167405531019 * 10 ^ 70 +
        7617354331997456402995847712985407743224103647410962956855120550222833) * 10 ^ 70 +
        6892323299913238513558423117926243289104738948518167146216367473210562) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 104 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_287 :
    recurrence2Scalar3Exceptional.coeff 287 =
      -(((14638312302715397192058998077447063626192 * 10 ^ 70 +
        4059532059740825907586964862370283250502706968103477698604622074365901) * 10 ^ 70 +
        5983297164628719853443954181732114203726336912094451173950679471893835) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 105 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 25 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_288 :
    recurrence2Scalar3Exceptional.coeff 288 =
      (((4129256506699342075029172631448412391283 * 10 ^ 70 +
        3140217455583524895730501831558550070736161830972436505605970788998127) * 10 ^ 70 +
        9304889061170227623053587699280265123915855145942027184071067818279833) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 106 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 24 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_289 :
    recurrence2Scalar3Exceptional.coeff 289 =
      -(((552377538546982097357194067603810352492 * 10 ^ 70 +
        9765745195469281976363353854365324414201342117208057269371144489786585) * 10 ^ 70 +
        7843181504283556937616277279806023350710816784305309817733636143991288) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 107 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 23 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_290 :
    recurrence2Scalar3Exceptional.coeff 290 =
      -(((186189464103484026421319825199632449151 * 10 ^ 70 +
        7920496574139078311027085966836097195789353811288288193065517230430367) * 10 ^ 70 +
        9001540431063093127958356934839097355873226555225512239515643808266835) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 108 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 22 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_291 :
    recurrence2Scalar3Exceptional.coeff 291 =
      (((165555835247616358499489248537370853720 * 10 ^ 70 +
        5817343160730388194297050752225670051818158473337035428927425502447020) * 10 ^ 70 +
        0782107622556683115109979606925145489893476286660456104824629720754862) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 109 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 21 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_292 :
    recurrence2Scalar3Exceptional.coeff 292 =
      -(((67622959534130947005903008044208317656 * 10 ^ 70 +
        2207033172792078322873303161881692231720954698420523420786971318798394) * 10 ^ 70 +
        0565887188907540338654593689809779873577049942183881154191741399023655) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 110 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 20 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_293 :
    recurrence2Scalar3Exceptional.coeff 293 =
      (((17624950041122965933668921664281184924 * 10 ^ 70 +
        0019240791013985302018178249395824452952494242290466323291610343689126) * 10 ^ 70 +
        8278799041433705540327067192628880216118931992132077916164232372914273) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 111 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 19 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_294 :
    recurrence2Scalar3Exceptional.coeff 294 =
      -(((2128343119554699645945926974941926143 * 10 ^ 70 +
        0396900154055749620209686282837450197829805819996892720085195662177579) * 10 ^ 70 +
        9821909930580855697817847350257808852913109442065107866737015191399549) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 112 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 18 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_295 :
    recurrence2Scalar3Exceptional.coeff 295 =
      -(((613337516852119081204956721738957064 * 10 ^ 70 +
        3450669184399919254628789971807204590355100911471904399129445455345908) * 10 ^ 70 +
        8065375900866066315345604894416517850984347589340962235172049929563959) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 113 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 17 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_296 :
    recurrence2Scalar3Exceptional.coeff 296 =
      (((470222574969730027558924601153272282 * 10 ^ 70 +
        6855258398603586321912800875612501591285470412259960812469243371127756) * 10 ^ 70 +
        5713278346492923871170408181595355135132205764112924363871912619612164) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 114 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_297 :
    recurrence2Scalar3Exceptional.coeff 297 =
      -(((158754859395659130822127352993248344 * 10 ^ 70 +
        9666503002201658591755041440409857497452676837606393443050665460760461) * 10 ^ 70 +
        5230435576381910148874089442107773554292132550887711331924653145725291) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 115 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 15 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
