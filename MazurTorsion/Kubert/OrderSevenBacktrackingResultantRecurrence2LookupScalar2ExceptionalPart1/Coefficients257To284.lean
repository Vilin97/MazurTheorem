/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Exceptional coefficient convolution

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
  recurrence2C2_coeff_0
  recurrence2C2_coeff_1
  recurrence2C2_coeff_2
  recurrence2C2_coeff_3
  recurrence2C2_coeff_4
  recurrence2C2_coeff_5
  recurrence2C2_coeff_6
  recurrence2C2_coeff_7
  recurrence2C2_coeff_8
  recurrence2C2_coeff_9
  recurrence2C2_coeff_10
  recurrence2C2_coeff_11
  recurrence2C2_coeff_12
  recurrence2C2_coeff_13
  recurrence2C2_coeff_14
  recurrence2C2_coeff_15
  recurrence2C2_coeff_16
  recurrence2C2_coeff_17
  recurrence2C2_coeff_18
  recurrence2C2_coeff_19
  recurrence2C2_coeff_20
  recurrence2C2_coeff_21
  recurrence2C2_coeff_22
  recurrence2C2_coeff_23
  recurrence2C2_coeff_24
  recurrence2C2_coeff_25
  recurrence2C2_coeff_26
  recurrence2C2_coeff_27
  recurrence2C2_coeff_28
  recurrence2C2_coeff_29
  recurrence2C2_coeff_30
  recurrence2C2_coeff_31
  recurrence2C2_coeff_32
  recurrence2C2_coeff_33
  recurrence2C2_coeff_34
  recurrence2C2_coeff_35
  recurrence2C2_coeff_36
  recurrence2C2_coeff_37
  recurrence2C2_coeff_38
  recurrence2C2_coeff_39
  recurrence2C2_coeff_40
  recurrence2C2_coeff_41
  recurrence2C2_coeff_42
  recurrence2C2_coeff_43
  recurrence2C2_coeff_44
  recurrence2C2_coeff_45
  recurrence2C2_coeff_46
  recurrence2C2_coeff_47
  recurrence2C2_coeff_48
  recurrence2C2_coeff_49
  recurrence2C2_coeff_50
  recurrence2C2_coeff_51
  recurrence2C2_coeff_52
  recurrence2C2_coeff_53
  recurrence2C2_coeff_54
  recurrence2C2_coeff_55
  recurrence2C2_coeff_56
  recurrence2C2_coeff_57
  recurrence2C2_coeff_58
  recurrence2C2_coeff_59
  recurrence2C2_coeff_60
  recurrence2C2_coeff_61
  recurrence2C2_coeff_62
  recurrence2C2_coeff_63
  recurrence2C2_coeff_64
  recurrence2C2_coeff_65
  recurrence2C2_coeff_66
  recurrence2C2_coeff_67
  recurrence2C2_coeff_68
  recurrence2C2_coeff_69
  recurrence2C2_coeff_70
  recurrence2C2_coeff_71
  recurrence2C2_coeff_72
  recurrence2C2_coeff_73
  recurrence2C2_coeff_74
  recurrence2C2_coeff_75
  recurrence2C2_coeff_76
  recurrence2C2_coeff_77
  recurrence2C2_coeff_78
  recurrence2C2_coeff_79
  recurrence2C2_coeff_80
  recurrence2C2_coeff_81
  recurrence2C2_coeff_82
  recurrence2C2_coeff_83
  recurrence2C2_coeff_84
  recurrence2C2_coeff_85
  recurrence2C2_coeff_86
  recurrence2C2_coeff_87
  recurrence2C2_coeff_88
  recurrence2C2_coeff_89
  recurrence2C2_coeff_90
  recurrence2C2_coeff_91
  recurrence2C2_coeff_92
  recurrence2C2_coeff_93
  recurrence2C2_coeff_94
  recurrence2C2_coeff_95
  recurrence2C2_coeff_96
  recurrence2C2_coeff_97
  recurrence2C2_coeff_98
  recurrence2C2_coeff_99
  recurrence2C2_coeff_100
  recurrence2C2_coeff_101
  recurrence2C2_coeff_102
  recurrence2C2_coeff_103
  recurrence2C2_coeff_104
  recurrence2C2_coeff_105
  recurrence2C2_coeff_106
  recurrence2C2_coeff_107
  recurrence2C2_coeff_108
  recurrence2C2_coeff_109
  recurrence2C2_coeff_110
  recurrence2C2_coeff_111
  recurrence2C2_coeff_112
  recurrence2C2_coeff_113
  recurrence2C2_coeff_114
  recurrence2C2_coeff_115
  recurrence2C2_coeff_116
  recurrence2C2_coeff_117
  recurrence2C2_coeff_118
  recurrence2C2_coeff_119
  recurrence2C2_coeff_120
  recurrence2C2_coeff_121
  recurrence2C2_coeff_122
  recurrence2C2_coeff_123
  recurrence2C2_coeff_124
  recurrence2C2_coeff_125
  recurrence2C2_coeff_126
  recurrence2C2_coeff_127
  recurrence2C2_coeff_128
  recurrence2C2_coeff_129
  recurrence2C2_coeff_130
  recurrence2C2_coeff_131
  recurrence2C2_coeff_132
  recurrence2C2_coeff_133
  recurrence2C2_coeff_134
  recurrence2C2_coeff_135
  recurrence2C2_coeff_136
  recurrence2C2_coeff_137
  recurrence2C2_coeff_138
  recurrence2C2_coeff_139
  recurrence2C2_coeff_140
  recurrence2C2_coeff_141
  recurrence2C2_coeff_142
  recurrence2C2_coeff_143
  recurrence2C2_coeff_144
  recurrence2C2_coeff_145
  recurrence2C2_coeff_146
  recurrence2C2_coeff_147
  recurrence2C2_coeff_148
  recurrence2C2_coeff_149
  recurrence2C2_coeff_150
  recurrence2C2_coeff_151
  recurrence2C2_coeff_152
  recurrence2C2_coeff_153
  recurrence2C2_coeff_154
  recurrence2C2_coeff_155
  recurrence2C2_coeff_156
  recurrence2C2_coeff_157
  recurrence2C2_coeff_158
  recurrence2C2_coeff_159
  recurrence2C2_coeff_160
  recurrence2C2_coeff_161
  recurrence2C2_coeff_162
  recurrence2C2_coeff_163
  recurrence2C2_coeff_164
  recurrence2C2_coeff_165
  recurrence2C2_coeff_166
  recurrence2C2_coeff_167
  recurrence2C2_coeff_168
  recurrence2C2_coeff_169
  recurrence2C2_coeff_170
  recurrence2C2_coeff_171
  recurrence2C2_coeff_172
  recurrence2C2_coeff_173
  recurrence2C2_coeff_174
  recurrence2C2_coeff_175
  recurrence2C2_coeff_176
  recurrence2C2_coeff_177
  recurrence2C2_coeff_178
  recurrence2C2_coeff_179
  recurrence2C2_coeff_180
  recurrence2C2_coeff_181
  recurrence2C2_coeff_182
  recurrence2C2_coeff_183
  recurrence2C2_coeff_184
  recurrence2C2_coeff_185
  recurrence2C2_coeff_186

private theorem recurrence2Scalar2Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (257 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_257 :
    recurrence2Scalar2Exceptional.coeff 257 =
      -(((439688309468970457290467341799760195914209488620361405 * 10 ^ 70 +
        8228296278715177774010074940222824785751632167332530700096951422916580) * 10 ^ 70 +
        3296610615662980405924855790257692289742979937134618903892841962500463) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 71 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 27 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_258 :
    recurrence2Scalar2Exceptional.coeff 258 =
      (((212793299342856833839053377369359954812545246831088850 * 10 ^ 70 +
        6924320038775870228568318110051656928227913419959171000390938550458077) * 10 ^ 70 +
        3973959554498507079704391899764656057231478408022155832792520558005351) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 72 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 26 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_259 :
    recurrence2Scalar2Exceptional.coeff 259 =
      -(((89796650442966042492913222341599518012241420245548091 * 10 ^ 70 +
        5891337298296137481289788308943370023565413723893320994988465211951526) * 10 ^ 70 +
        5308220239643347198045810406962250625220096152104806920613216624424665) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 73 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 25 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_260 :
    recurrence2Scalar2Exceptional.coeff 260 =
      (((32670760570195642837953305445026011550662441711621570 * 10 ^ 70 +
        7213651909317300319897475599737807550251067486617605511237075019542239) * 10 ^ 70 +
        8301264490853517831359689119183250099958209677052371402933209048206923) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 74 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 24 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_261 :
    recurrence2Scalar2Exceptional.coeff 261 =
      -(((9629091384981221792945180894991288782551293101037913 * 10 ^ 70 +
        2549968104166771050195079462061790250553284878627191600018099768368131) * 10 ^ 70 +
        2487901249822569919376615193560309337268698524007589423230398827760830) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 75 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 23 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_262 :
    recurrence2Scalar2Exceptional.coeff 262 =
      (((1750371422170842361714800837589581261180070468565533 * 10 ^ 70 +
        6665688942068635049271586908729732158280272191767666350871710202061825) * 10 ^ 70 +
        0149781354541365110004574037680526764548743521297351703162580697703675) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 76 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 22 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_263 :
    recurrence2Scalar2Exceptional.coeff 263 =
      (((311965556430972384890604735726328773865185986817609 * 10 ^ 70 +
        0141667749943978102712380711894594884241684442448906537732361093846613) * 10 ^ 70 +
        0028190238908208748308300553723012666054616223540613355544030274909734) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 77 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 21 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_264 :
    recurrence2Scalar2Exceptional.coeff 264 =
      -(((530593836264933805365345827550430853322105393301232 * 10 ^ 70 +
        9465433175806202156833823104690481772261808112947411650417158760516066) * 10 ^ 70 +
        1842931897963653295628711522453311309777225810607293550021698974436453) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 78 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 20 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_265 :
    recurrence2Scalar2Exceptional.coeff 265 =
      (((344900487900388824079563653599170651304621552848195 * 10 ^ 70 +
        4990805701451841201376692276877091939457849430951773547634545317289417) * 10 ^ 70 +
        6174750003323999466618129246905499660870774526589479097109943718056766) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 79 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 19 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_266 :
    recurrence2Scalar2Exceptional.coeff 266 =
      -(((168843619826711632991801451029881002578671303643594 * 10 ^ 70 +
        4386899281386328292171139475308777512533033497316715531745830023903188) * 10 ^ 70 +
        3986433291849433356826725922318979804419394895635028339190110053892290) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 80 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 18 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_267 :
    recurrence2Scalar2Exceptional.coeff 267 =
      (((68827501250110407117028171692860032756756823453333 * 10 ^ 70 +
        1123763538547862227685443333701360152061694768266266893909211646796239) * 10 ^ 70 +
        0713083549240207410483667755423508443003796343996702042121345776943922) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 81 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 17 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_268 :
    recurrence2Scalar2Exceptional.coeff 268 =
      -(((23897471023767231508586826957211613256505680049936 * 10 ^ 70 +
        9721335523748634200613455940835276117301732243862806000163789052137638) * 10 ^ 70 +
        7829393622651725514071199110499352037088848710743179732613579609276561) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 82 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 16 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_269 :
    recurrence2Scalar2Exceptional.coeff 269 =
      (((7038837491558450252619125080474731257040841336741 * 10 ^ 70 +
        6676116419338913528571475630298854320046143680550903912528630850076874) * 10 ^ 70 +
        9582412292501191161390194891102133710704534532436529146301104229707606) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 83 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 15 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_270 :
    recurrence2Scalar2Exceptional.coeff 270 =
      -(((1746393425905647613515845202106618740503723736385 * 10 ^ 70 +
        7009658367351753951477926860145834672901493435508128306786897176716077) * 10 ^ 70 +
        2900417195389137122211906966004115437422826522508596767805569491363583) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 84 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 14 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_271 :
    recurrence2Scalar2Exceptional.coeff 271 =
      (((390944837008536232662200418259289054631123054882 * 10 ^ 70 +
        1964530823471878737561806702046711609035510425537253479002112363635994) * 10 ^ 70 +
        4938213873693654067990970762265683752355175574961785316913614116359750) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 85 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 13 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_272 :
    recurrence2Scalar2Exceptional.coeff 272 =
      -(((113024002451601375880740502017451322805264006243 * 10 ^ 70 +
        5549631949093500117094425653280102997951293754425492755380009118586804) * 10 ^ 70 +
        4520822839009768323026951652118445336874033549833283145571774664914061) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 86 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 12 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_273 :
    recurrence2Scalar2Exceptional.coeff 273 =
      (((54578357646183583908814843173658143338836623820 * 10 ^ 70 +
        0875678996264384971548501836692291919528240646357217554455255570547747) * 10 ^ 70 +
        9441764058022994076601200857197703723806320497807364593089102755493746) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 87 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 11 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_274 :
    recurrence2Scalar2Exceptional.coeff 274 =
      -(((26945752836193164093020437500440587107554070550 * 10 ^ 70 +
        0726147044359837993376344538995050594119558947487657511596902012883421) * 10 ^ 70 +
        7185059484763680282055191896947856342241866841598239309126333044616395) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 88 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 10 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_275 :
    recurrence2Scalar2Exceptional.coeff 275 =
      (((8125753056556697696286732239201468392565493961 * 10 ^ 70 +
        4890535602100244361055489869159037775607425228510346612698022404880305) * 10 ^ 70 +
        2696478741282741373582026389571176611607522054478956877284687168130861) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 89 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 9 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_276 :
    recurrence2Scalar2Exceptional.coeff 276 =
      (((1414821526824699234413477378851705996946437498 * 10 ^ 70 +
        3988847926998264904420812616455481670501936119731102472145530601453763) * 10 ^ 70 +
        5740802343277538850478148785703489213456090085940751481834335761444350) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 90 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 8 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_277 :
    recurrence2Scalar2Exceptional.coeff 277 =
      -(((4005897262975037512738367681893531637341087802 * 10 ^ 70 +
        3666267877802618502940727959004250313795220565008300393179049743821181) * 10 ^ 70 +
        2826913761681242856050004997389573274170639873691891856265055216087814) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 91 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 7 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_278 :
    recurrence2Scalar2Exceptional.coeff 278 =
      (((3345228176540276371804741579384905786910690115 * 10 ^ 70 +
        8091770215939509636498199720113857805202134101819598454380679065760824) * 10 ^ 70 +
        4815717875865776648617614977250162158204430337929611262469048394757410) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 92 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 6 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_279 :
    recurrence2Scalar2Exceptional.coeff 279 =
      -(((1964953887887406427598277797666706172820992710 * 10 ^ 70 +
        8603448283168380876555493127483902713906134660144075735188287850245442) * 10 ^ 70 +
        7232176255467159379927605722526921179196815552226804679418289267752150) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 93 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 5 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_280 :
    recurrence2Scalar2Exceptional.coeff 280 =
      (((904438307255582041257839467120960677392282539 * 10 ^ 70 +
        1655162185406202790618320526959502080258727125908627961350701376451943) * 10 ^ 70 +
        7069199870127777124794384727291867460378772238143332330381476468786972) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 94 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 4 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_281 :
    recurrence2Scalar2Exceptional.coeff 281 =
      -(((323895734877359746477971086231382821598918158 * 10 ^ 70 +
        0131457589661761409002917386012765671400736141817959961970710727587314) * 10 ^ 70 +
        8056487936212359319372915938825842440510833476929630821169993542007058) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 95 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 3 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_282 :
    recurrence2Scalar2Exceptional.coeff 282 =
      (((77209092170927876593462980052832546108579289 * 10 ^ 70 +
        0900392085186915865007729425404645451442029103257006866454581131907521) * 10 ^ 70 +
        4474027313445616442924790417107559667198055869223828574517423479421836) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 96 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 2 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_283 :
    recurrence2Scalar2Exceptional.coeff 283 =
      (((1026043635217218094887550433735033242777295 * 10 ^ 70 +
        5811836313511546457770352172072429058740824275184913988241240623813204) * 10 ^ 70 +
        6364934251767483307813183255812898152639716433957143792664971511551465) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 97 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 1 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_284 :
    recurrence2Scalar2Exceptional.coeff 284 =
      -(((14233189156523677521421212883005881549755041 * 10 ^ 70 +
        5074034108029359172357253726307860658364889863922691084341291308018545) * 10 ^ 70 +
        8651973453690273369461242749001231139922346466663166746689663254432381) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 98 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
