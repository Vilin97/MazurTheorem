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

private theorem recurrence2Scalar2Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_285 :
    recurrence2Scalar2Exceptional.coeff 285 =
      (((10027854606738741094584063892338723108987245 * 10 ^ 70 +
        1718558507137470627072866287852645029894716370506432677232440970315351) * 10 ^ 70 +
        3828484254346483336435798836344504144648242901799781088373013476966836) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 99 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 31 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_286 :
    recurrence2Scalar2Exceptional.coeff 286 =
      -(((4737633970617453263620236143868099127029615 * 10 ^ 70 +
        1546706873029290775832932382181900502644857011476370464316347656290501) * 10 ^ 70 +
        3498438095029078861643331683345406594164154933761678198605528370381415) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 100 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 30 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_287 :
    recurrence2Scalar2Exceptional.coeff 287 =
      (((1699741327005970739476457715555518169130804 * 10 ^ 70 +
        3498878829645622018045199387198646972400780998077177206733890379322931) * 10 ^ 70 +
        1826921932932058539486640703834306185075194812753329674904960941137023) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 101 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 29 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_288 :
    recurrence2Scalar2Exceptional.coeff 288 =
      -(((439600394059449182657731189733529940535252 * 10 ^ 70 +
        9317376724555468455319228142615956466048306306866880581336226545718742) * 10 ^ 70 +
        4157099471201440697344912370621256829845498462499933218512978361188800) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 102 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 28 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_289 :
    recurrence2Scalar2Exceptional.coeff 289 =
      (((49026373579864332843063895555217624257928 * 10 ^ 70 +
        8350860472759634925502156710097943482413739150979812994978186185758902) * 10 ^ 70 +
        5996896103798233887009674661977766482365347045339498257386248282417898) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 103 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 27 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_290 :
    recurrence2Scalar2Exceptional.coeff 290 =
      (((26609312891049027578063872129770689035510 * 10 ^ 70 +
        2743004588636872224777139057522188025626095445764303671102615806520951) * 10 ^ 70 +
        4055708160750659261282257969964837607498819728621968995782715131669864) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 104 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 26 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_291 :
    recurrence2Scalar2Exceptional.coeff 291 =
      -(((21978527562175569443283712955674585502311 * 10 ^ 70 +
        1851652782489799665642676996609514932132280767178312662015020429255369) * 10 ^ 70 +
        2176710696081443963106681632602460442168960806112433639967028760057350) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 105 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 25 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_292 :
    recurrence2Scalar2Exceptional.coeff 292 =
      (((9625012012044214306083008292549816726903 * 10 ^ 70 +
        2155917649770241408534876025739050804998466373567719375536429095927802) * 10 ^ 70 +
        6551165033792024891986779088058998650483179002444033823703100303826605) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 106 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 24 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_293 :
    recurrence2Scalar2Exceptional.coeff 293 =
      -(((2946652673882779575915358828464182652288 * 10 ^ 70 +
        1843731659658036770790063472516463483196886987070404741679160481191739) * 10 ^ 70 +
        2155613347620943275934729305300642689043812188636972957284705681396167) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 107 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 23 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_294 :
    recurrence2Scalar2Exceptional.coeff 294 =
      (((574888698355983469906374561152230524043 * 10 ^ 70 +
        0322353608815529129874783518329749854556037023047251248337521725769553) * 10 ^ 70 +
        0549777032444000284760621425730272628122080330239962630686911705781441) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 108 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 22 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_295 :
    recurrence2Scalar2Exceptional.coeff 295 =
      -(((2281792391198616732491703663866644051 * 10 ^ 70 +
        8978463875407283797950755039804717958722103123619577849093699500326532) * 10 ^ 70 +
        0759427117807614887513696267817800386754495842245915569780325467675133) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 109 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 21 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_296 :
    recurrence2Scalar2Exceptional.coeff 296 =
      -(((54912379832166583096012259532806802666 * 10 ^ 70 +
        9692949320153554905179648630328886920255554134332429607483414476482599) * 10 ^ 70 +
        0640378609853263786187569826294000535197541563818333003430930826664284) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 110 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 20 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_297 :
    recurrence2Scalar2Exceptional.coeff 297 =
      (((27398944128386042751714383532672033653 * 10 ^ 70 +
        2510397270619468062018300308836295165556487328563028311362645129981963) * 10 ^ 70 +
        3724582047176747472340806179164853451312332797098943259234416484688088) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 111 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 19 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_298 :
    recurrence2Scalar2Exceptional.coeff 298 =
      -(((8260073726373629222334366477333473922 * 10 ^ 70 +
        3860338333524948030752850630526214531889923061001947835392702781543732) * 10 ^ 70 +
        2804717156293907607663160890172709746914353076035531317211003541136700) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 112 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 18 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_299 :
    recurrence2Scalar2Exceptional.coeff 299 =
      (((1516622296025270646006076900723155588 * 10 ^ 70 +
        2248187409539777745055127912521488005285604513217411713079964649918927) * 10 ^ 70 +
        1076804583297964541938098919224148711199815377314899323543586228439803) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 113 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 17 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_300 :
    recurrence2Scalar2Exceptional.coeff 300 =
      -(((17568907265820501076075392798108511 * 10 ^ 70 +
        0867466793639262722197490607441697422906255631927282708141088217730289) * 10 ^ 70 +
        2019354141304949251000712114162774207632200018685790496559277879395638) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 114 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 16 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_301 :
    recurrence2Scalar2Exceptional.coeff 301 =
      -(((107242287369794411994067759317872990 * 10 ^ 70 +
        3044547510511204084193460779362101002817473610495284681635842262449184) * 10 ^ 70 +
        7160632318481854947295798570362411704319897489395903424956067825547149) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 115 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 15 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_302 :
    recurrence2Scalar2Exceptional.coeff 302 =
      (((45682872420415285193470592772612877 * 10 ^ 70 +
        2135595369692850840891768474357016445585284425691980245112657103796933) * 10 ^ 70 +
        1028499134411522201247859859145974176870422637514366695242854475186814) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 116 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 14 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_303 :
    recurrence2Scalar2Exceptional.coeff 303 =
      -(((10918299824118076270698777157050231 * 10 ^ 70 +
        7011560065044214924421614085572622645349190106786949197293210928255555) * 10 ^ 70 +
        5617247021703847301228555328162464789656395823550129269421305433472806) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 117 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 13 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_304 :
    recurrence2Scalar2Exceptional.coeff 304 =
      (((1243697152248162409097199484491549 * 10 ^ 70 +
        4846557356912137538541444121235685086825028276051532768932566014340675) * 10 ^ 70 +
        3153144841829562575194907600549541184588757579892755445842487196201465) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 118 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 12 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_305 :
    recurrence2Scalar2Exceptional.coeff 305 =
      (((207079654429976399587512395649315 * 10 ^ 70 +
        3961936504228315951880209027057255985183245429615683342890393331026268) * 10 ^ 70 +
        5470094611408159853052286147015835026403977616704034115791091570469754) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 119 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 11 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_306 :
    recurrence2Scalar2Exceptional.coeff 306 =
      -(((144721731307245425688924475436016 * 10 ^ 70 +
        0405244817553716671767509650929169619184268379603477319447826475067802) * 10 ^ 70 +
        3485593843377110632126429889128129853813280765605313188864236231752686) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 120 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 10 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_307 :
    recurrence2Scalar2Exceptional.coeff 307 =
      (((37721906242627070918398248788349 * 10 ^ 70 +
        6118606748813566225127723508021844575558692311278802274749872516465016) * 10 ^ 70 +
        5249822893526863452343291654090999238245135578101802091962189762474101) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 121 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 9 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_308 :
    recurrence2Scalar2Exceptional.coeff 308 =
      -(((4793882870634908732974260026033 * 10 ^ 70 +
        0006067197530168657391425801953045038772975877248104188741813694505597) * 10 ^ 70 +
        8493558756683604042196461945900929274849821264626593532270284698644374) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 122 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 8 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_309 :
    recurrence2Scalar2Exceptional.coeff 309 =
      -(((341055477333835379312982797581 * 10 ^ 70 +
        1852508280364400357626789282990665954806341116382362142828123443014559) * 10 ^ 70 +
        9034721131345781953430153361165354656781632022706874297778424820782777) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 123 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 7 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_310 :
    recurrence2Scalar2Exceptional.coeff 310 =
      (((319549007103991988280575184643 * 10 ^ 70 +
        2067137556743691159813098383200953193751311930355377276310129675182644) * 10 ^ 70 +
        9622851273948836728871159034702836350784015491009034727301566342985058) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 124 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 6 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_311 :
    recurrence2Scalar2Exceptional.coeff 311 =
      -(((75438669017306721536332785106 * 10 ^ 70 +
        3885633399216576960262655088821238528906723870301825555169465874121121) * 10 ^ 70 +
        0924393440293512341113189709541767799260730758397523796273664392102832) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 125 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 5 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_312 :
    recurrence2Scalar2Exceptional.coeff 312 =
      (((7325747123534633412076998504 * 10 ^ 70 +
        3746468246706505382426320275729265952334660836582114254882779232021504) * 10 ^ 70 +
        6727790977837840353528182194941643815783933605529161739731290454646249) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 126 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 4 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_313 :
    recurrence2Scalar2Exceptional.coeff 313 =
      (((1000147800224175411643826818 * 10 ^ 70 +
        9043687577881766270142320648690527372734333137697200956966511171206472) * 10 ^ 70 +
        7857335604985078696223457573314768086878369736998644867378666449549620) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 127 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 3 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
