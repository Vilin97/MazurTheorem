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

private theorem recurrence2Scalar2Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (314 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_314 :
    recurrence2Scalar2Exceptional.coeff 314 =
      -(((503827678286081861419181200 * 10 ^ 70 +
        3873770195029118539497150999479055948709431657451508423398736654673839) * 10 ^ 70 +
        9400847465155178659842049763591129896854138840861657759444710851116474) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 128 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 2 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (315 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_315 :
    recurrence2Scalar2Exceptional.coeff 315 =
      (((81874804671940265859552595 * 10 ^ 70 +
        2940594855773183558550468883513479032229011311922027234019831662801486) * 10 ^ 70 +
        2203629483672929620340955531348266266747101554952355248808708105741723) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 129 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 1 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (316 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_316 :
    recurrence2Scalar2Exceptional.coeff 316 =
      -(((1854921481429163296578276 * 10 ^ 70 +
        5345802574154246197682176010546961618980411691008201391794121397841753) * 10 ^ 70 +
        3072158993789098474030836265010762378892934662538971996839486647621600) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 130 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (317 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_317 :
    recurrence2Scalar2Exceptional.coeff 317 =
      -(((2041588420925511602295904 * 10 ^ 70 +
        3091104615110597065651336924240675708877819667294122198227775803559838) * 10 ^ 70 +
        6355012738197634975187086521258017155458588349238553315716104106330208) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 131 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 31 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (318 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_318 :
    recurrence2Scalar2Exceptional.coeff 318 =
      (((443901168895715940596470 * 10 ^ 70 +
        6614587604652287620609300110635361468277644733037212388738725016623264) * 10 ^ 70 +
        1462976226712179521956939669561199716043138225231778436067463492313805) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 132 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 30 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (319 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_319 :
    recurrence2Scalar2Exceptional.coeff 319 =
      -(((27134951489994032037365 * 10 ^ 70 +
        6473867892700604121629228343354462806885491122348807827356535898174891) * 10 ^ 70 +
        6113726626456556925360461914940987990235102167477378537388231646684703) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 133 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 29 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (320 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_320 :
    recurrence2Scalar2Exceptional.coeff 320 =
      -(((6187189960839707899084 * 10 ^ 70 +
        6599709173011766837389482096541967082820145624610700447172363342636122) * 10 ^ 70 +
        0141104337898856946390686786355052302534611111389488840290812045730926) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 134 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 28 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (321 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_321 :
    recurrence2Scalar2Exceptional.coeff 321 =
      (((1588699909188841273318 * 10 ^ 70 +
        5474218913114297859260526797433862144124635876101131200697956236737718) * 10 ^ 70 +
        9142919520153942995640653867680133224076099311725918756274031308274809) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 135 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 27 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (322 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_322 :
    recurrence2Scalar2Exceptional.coeff 322 =
      -(((101481457762941132160 * 10 ^ 70 +
        2840353776763065024117075130565495359665520764309341686316806106067232) * 10 ^ 70 +
        9022371488032118550753934695269027021419536277126658406805376922392218) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 136 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 26 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (323 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_323 :
    recurrence2Scalar2Exceptional.coeff 323 =
      -(((17561880775566355960 * 10 ^ 70 +
        8616931982216303016934833460197368634298373512464469837647517464364244) * 10 ^ 70 +
        4684332835458169133811892998125500363697209300383805229923882655813264) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 137 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 25 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (324 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_324 :
    recurrence2Scalar2Exceptional.coeff 324 =
      (((4041281742346528630 * 10 ^ 70 +
        6135049135662906137328271776742333701432309901728959262224795297059709) * 10 ^ 70 +
        1023799262206490179838949662159793471531510139304941553802303972173564) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 138 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 24 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (325 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_325 :
    recurrence2Scalar2Exceptional.coeff 325 =
      -(((160527860315960745 * 10 ^ 70 +
        0524141624947267914503866578330226860902052500544048389063137786389814) * 10 ^ 70 +
        8937792673386279182552423377789813949588346590991584635799750696054742) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 139 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 23 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (326 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_326 :
    recurrence2Scalar2Exceptional.coeff 326 =
      -(((47153268548959551 * 10 ^ 70 +
        3215561545237843842076470882990880715809366050712617455883523440972592) * 10 ^ 70 +
        4939559656190074002570915156448662777996123054821870413965581827857246) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 140 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 22 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (327 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_327 :
    recurrence2Scalar2Exceptional.coeff 327 =
      (((6712575433197638 * 10 ^ 70 +
        8326404438058031696076564364111840924056898512247789580629953581136490) * 10 ^ 70 +
        9818514196254695622459819542970446264317495851706802281029702863958508) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 141 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 21 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (328 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_328 :
    recurrence2Scalar2Exceptional.coeff 328 =
      (((81648056469271 * 10 ^ 70 +
        2595379780390210409529114398557938121512491021963114891932671003096864) * 10 ^ 70 +
        9484601689249367666421579267058260698066865715289351180839550586300213) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 142 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 20 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (329 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_329 :
    recurrence2Scalar2Exceptional.coeff 329 =
      -(((89262648552405 * 10 ^ 70 +
        2792004565259237661434272160643303397725626293875118579486401385834291) * 10 ^ 70 +
        3383575014208170786683047981071325447243434978629651720120689295704735) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 143 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 19 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (330 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_330 :
    recurrence2Scalar2Exceptional.coeff 330 =
      (((4639044415097 * 10 ^ 70 +
        9114074009289438795816452047849651944585668861513437640410751998861484) * 10 ^ 70 +
        2557039255745059819744471939410083969131012914294262513745636068671364) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 144 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 18 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (331 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_331 :
    recurrence2Scalar2Exceptional.coeff 331 =
      (((691922017134 * 10 ^ 70 +
        0560863286456180109081415362086316046011366050144294052414888323091487) * 10 ^ 70 +
        3301731473492119434199349174736270383882670860719929535756477339179990) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 145 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 17 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (332 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_332 :
    recurrence2Scalar2Exceptional.coeff 332 =
      -(((74241271280 * 10 ^ 70 +
        1078647055191145241486837881576374068306057062648685578263629138753403) * 10 ^ 70 +
        9696888586343843885035762381818987947530388635942916288263673382564981) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 146 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 16 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (333 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_333 :
    recurrence2Scalar2Exceptional.coeff 333 =
      -(((3595112029 * 10 ^ 70 +
        1555374239196846082016745797945157302760803683815682692849143144823649) * 10 ^ 70 +
        5915083025241793239575661141093882876411387993846649324447890494299481) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 147 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 15 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (334 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_334 :
    recurrence2Scalar2Exceptional.coeff 334 =
      (((679872738 * 10 ^ 70 +
        7754718101402708804413254067351169707314128279605688770038604004300607) * 10 ^ 70 +
        0745818085278001388655391407549302158060065280630455711748531027663626) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 148 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 14 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (335 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_335 :
    recurrence2Scalar2Exceptional.coeff 335 =
      (((16197704 * 10 ^ 70 +
        6768973851853435736393715300983848614802441708067725624447563730070321) * 10 ^ 70 +
        3950153860946403960214952123214000148090160558327161234325295142703823) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 149 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 13 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (336 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_336 :
    recurrence2Scalar2Exceptional.coeff 336 =
      -(((4572633 * 10 ^ 70 +
        7784254466913461102999366801942464567977141162664759924101983354974544) * 10 ^ 70 +
        5610822013086164307310551714031069704112627423408848384823202318509634) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 150 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 12 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (337 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_337 :
    recurrence2Scalar2Exceptional.coeff 337 =
      -(((112982 * 10 ^ 70 +
        8337057345435346358397858949235040041747700550028879317533529564063363) * 10 ^ 70 +
        5225460215372303330899400630447454262589255568627862584027447159816074) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 151 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 11 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (338 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_338 :
    recurrence2Scalar2Exceptional.coeff 338 =
      (((23185 * 10 ^ 70 +
        6735981271520416066333099065496666802054751968227178209889636585337185) * 10 ^ 70 +
        1675657012242528279952320903575146880331016033811911010590370794584640) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 152 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 10 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (339 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_339 :
    recurrence2Scalar2Exceptional.coeff 339 =
      (((1039 * 10 ^ 70 +
        9781891876917199543588072166625991872395517851848586788738788600457363) * 10 ^ 70 +
        4979117664704555420296546802829979440569581136161240416210261051084317) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 153 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 9 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (340 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_340 :
    recurrence2Scalar2Exceptional.coeff 340 =
      -(((69 * 10 ^ 70 +
        3717768677907796179106394124797276976959534640659469338356425284537691) * 10 ^ 70 +
        7021872789177325900142147925213087417632619477454598700810952796987930) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 154 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 8 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (341 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_341 :
    recurrence2Scalar2Exceptional.coeff 341 =
      -(((6 * 10 ^ 70 +
        6980414870611092264442604467484695653355088685936768213774715847923149) * 10 ^ 70 +
        5058408370098138833412759135554622071460741471808900142770055133676416) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 155 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 7 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (342 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_342 :
    recurrence2Scalar2Exceptional.coeff 342 =
      -((748679152607287457807778457278076588548978525043425402850874413050888 * 10 ^ 70 +
        6209712514867602247553706446209735687875875925975061109107361404701243) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 156 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 6 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (343 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_343 :
    recurrence2Scalar2Exceptional.coeff 343 =
      ((163623862041576463861203973984003809215600272248035244499787880393168 * 10 ^ 70 +
        1940875455571545615266833181670556662202124972668346917789218864680711) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 157 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 5 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
