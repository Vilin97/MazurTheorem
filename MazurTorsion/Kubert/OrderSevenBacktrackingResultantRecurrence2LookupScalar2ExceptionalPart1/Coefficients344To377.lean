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

private theorem recurrence2Scalar2Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (344 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_344 :
    recurrence2Scalar2Exceptional.coeff 344 =
      ((12387351213659236688827127381171112846799816621661115770639299111840 * 10 ^ 70 +
        5902240693279949211476556074035446755235851460301672558579320349859255) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 158 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 4 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (345 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_345 :
    recurrence2Scalar2Exceptional.coeff 345 =
      ((494548013231565395394107373421615793511138909707598009537089575921 * 10 ^ 70 +
        3034748068525241023522940557143326569051333117318741115595084901659581) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 159 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 3 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (346 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_346 :
    recurrence2Scalar2Exceptional.coeff 346 =
      ((13365873373330739878179506549138585973177428841577903932735929243 * 10 ^ 70 +
        2666511819353181512383642559429154305734432958482323157590951673630501) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 160 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 2 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (347 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_347 :
    recurrence2Scalar2Exceptional.coeff 347 =
      ((264160985651744138756551342727776215151358686633982823516423887 * 10 ^ 70 +
        5579500358120864219861411287218573380822193671604203952192937935085763) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 161 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 1 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (348 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_348 :
    recurrence2Scalar2Exceptional.coeff 348 =
      ((3948995606126024970098649907620749511263851955910272821226198 * 10 ^ 70 +
        9355177002011220713850889559874921706773609028049948168606566272191974) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 162 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (349 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_349 :
    recurrence2Scalar2Exceptional.coeff 349 =
      ((45339652873347273149867910428040122752534126599380971127560 * 10 ^ 70 +
        8653719969580976206665364906459004592575218925569135949224779488289980) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 163 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 31 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (350 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_350 :
    recurrence2Scalar2Exceptional.coeff 350 =
      ((401307901716500964548974295605753104973619798333321795107 * 10 ^ 70 +
        8242097586250307910562702375286408114539165670721226853587148958777407) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 164 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 30 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (351 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_351 :
    recurrence2Scalar2Exceptional.coeff 351 =
      ((2719335999002904031005162749530880496401404482726734535 * 10 ^ 70 +
        4993840098068632215930929389097336697496227500927478679652414130364459) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 165 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 29 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (352 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_352 :
    recurrence2Scalar2Exceptional.coeff 352 =
      ((13795034372967129382657265828146525930857481106554678 * 10 ^ 70 +
        5716063097865545784239903109754676841996864905055431331443050187237221) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 166 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 28 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (353 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_353 :
    recurrence2Scalar2Exceptional.coeff 353 =
      ((49553170761641731863484230696599034569939122930788 * 10 ^ 70 +
        7781818893157203091564039291023351765722657532902138818823503415218158) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 167 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 27 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (354 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_354 :
    recurrence2Scalar2Exceptional.coeff 354 =
      ((105955811055547107893414390342643991025155706551 * 10 ^ 70 +
        7244763397927060737108464853793426419393748196308448367556021958801914) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 168 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 26 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (355 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_355 :
    recurrence2Scalar2Exceptional.coeff 355 =
      ((7779002332430986798519543214975032154800212 * 10 ^ 70 +
        0847884125149123577925845305778401845553841375813171038872049539711815) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 169 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 25 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (356 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_356 :
    recurrence2Scalar2Exceptional.coeff 356 =
      -((808551181130801562239590434121771772549477 * 10 ^ 70 +
        5749003002019338954653013782067216339100296379665933870167525091491949) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 170 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 24 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (357 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_357 :
    recurrence2Scalar2Exceptional.coeff 357 =
      -((2754251321055780819019260661329039268617 * 10 ^ 70 +
        0210473544075210447684945372960852010129717301192866515659086881729078) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 171 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 23 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (358 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_358 :
    recurrence2Scalar2Exceptional.coeff 358 =
      -((3640057198288236179019275002568996126 * 10 ^ 70 +
        1196357439218105547322658464425099995672100146339681821695956651339275) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 172 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 22 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (359 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_359 :
    recurrence2Scalar2Exceptional.coeff 359 =
      ((2824238433225707664744922431106061 * 10 ^ 70 +
        5734950421248152638906169625188004212011211753931374525279979169487106) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 173 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 21 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (360 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_360 :
    recurrence2Scalar2Exceptional.coeff 360 =
      ((18994595696398195247723682660733 * 10 ^ 70 +
        0928873038737495368147183637558106952681297415601571134311113643941804) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 174 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 20 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (361 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_361 :
    recurrence2Scalar2Exceptional.coeff 361 =
      ((29144579970527653714923396134 * 10 ^ 70 +
        4130665300809468579287338449034406691646287766139051989645968266154668) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 175 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 19 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (362 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_362 :
    recurrence2Scalar2Exceptional.coeff 362 =
      ((9053918625925141626809973 * 10 ^ 70 +
        7135055268818391812362177671830363951676131520446059596989151666573241) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 176 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 18 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (363 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_363 :
    recurrence2Scalar2Exceptional.coeff 363 =
      -((35280548029742859454540 * 10 ^ 70 +
        6358957843728032318865852295968139734841458333820183245904106306173142) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 177 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 17 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (364 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_364 :
    recurrence2Scalar2Exceptional.coeff 364 =
      -((63156253612457086367 * 10 ^ 70 +
        8161120249499894513630170248451432351253829142799837560657556445338579) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 178 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 16 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (365 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_365 :
    recurrence2Scalar2Exceptional.coeff 365 =
      -((52829565754715974 * 10 ^ 70 +
        9019211172547558201740171096710915743539120006494875860121405615200455) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 179 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 15 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (366 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_366 :
    recurrence2Scalar2Exceptional.coeff 366 =
      -((25842362623700 * 10 ^ 70 +
        7036621456356761267183215270050486679792628521864636900469230871580923) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 180 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 14 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (367 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_367 :
    recurrence2Scalar2Exceptional.coeff 367 =
      -((7665325702 * 10 ^ 70 +
        1323102776661730666047519427909966123087642633989179362324275719891139) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 181 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 13 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (368 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_368 :
    recurrence2Scalar2Exceptional.coeff 368 =
      -((1361718 * 10 ^ 70 +
        2111718329293120772884893782566007878961251386021098287957266254066632) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 182 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 12 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (369 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_369 :
    recurrence2Scalar2Exceptional.coeff 369 =
      -((140 * 10 ^ 70 +
        7225299108895109598663058466640247395724471499732668118017745440542151) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 183 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 11 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (370 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_370 :
    recurrence2Scalar2Exceptional.coeff 370 =
      (-81868686228454203299039834674591618851832451577061332668030070126200 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 184 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 10 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (371 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_371 :
    recurrence2Scalar2Exceptional.coeff 371 =
      (-2505467286567715828679445105200296487845655259314399725987942672 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 185 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 9 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (372 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_372 :
    recurrence2Scalar2Exceptional.coeff 372 =
      (-35272625218556995847679522300422653934473812817667793754774 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 186 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 8 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (373 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_373 :
    recurrence2Scalar2Exceptional.coeff 373 =
      (-210015516513919244718194431875260172136175321293110433 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 187 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 7 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (374 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_374 :
    recurrence2Scalar2Exceptional.coeff 374 =
      (-558380106899000772440910619237484769080014123044 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 188 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 6 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (375 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_375 :
    recurrence2Scalar2Exceptional.coeff 375 =
      (-589884556831854449741078234015576543128996 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 189 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (376 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_376 :
    recurrence2Scalar2Exceptional.coeff 376 =
      (-111005000805264452755470793520906832 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 190 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 4 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (377 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_377 :
    recurrence2Scalar2Exceptional.coeff 377 =
      (-845310990356491934016919003 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 191 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 3 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
