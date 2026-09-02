/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3ShiftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B2_coeff_0
  recurrence2B2_coeff_1
  recurrence2B2_coeff_2
  recurrence2B2_coeff_3
  recurrence2B2_coeff_4
  recurrence2B2_coeff_5
  recurrence2B2_coeff_6
  recurrence2B2_coeff_7
  recurrence2B2_coeff_8
  recurrence2B2_coeff_9
  recurrence2B2_coeff_10
  recurrence2B2_coeff_11
  recurrence2B2_coeff_12
  recurrence2B2_coeff_13
  recurrence2B2_coeff_14
  recurrence2B2_coeff_15
  recurrence2B2_coeff_16
  recurrence2B2_coeff_17
  recurrence2B2_coeff_18
  recurrence2B2_coeff_19
  recurrence2B2_coeff_20
  recurrence2B2_coeff_21
  recurrence2B2_coeff_22
  recurrence2B2_coeff_23
  recurrence2B2_coeff_24
  recurrence2B2_coeff_25
  recurrence2B2_coeff_26
  recurrence2B2_coeff_27
  recurrence2B2_coeff_28
  recurrence2B2_coeff_29
  recurrence2B2_coeff_30
  recurrence2B2_coeff_31
  recurrence2B2_coeff_32
  recurrence2B2_coeff_33
  recurrence2B2_coeff_34
  recurrence2B2_coeff_35
  recurrence2B2_coeff_36
  recurrence2B2_coeff_37
  recurrence2B2_coeff_38
  recurrence2B2_coeff_39
  recurrence2B2_coeff_40
  recurrence2B2_coeff_41
  recurrence2B2_coeff_42
  recurrence2B2_coeff_43
  recurrence2B2_coeff_44
  recurrence2B2_coeff_45
  recurrence2B2_coeff_46
  recurrence2B2_coeff_47
  recurrence2B2_coeff_48
  recurrence2B2_coeff_49
  recurrence2B2_coeff_50
  recurrence2B2_coeff_51
  recurrence2B2_coeff_52
  recurrence2B2_coeff_53
  recurrence2B2_coeff_54
  recurrence2B2_coeff_55
  recurrence2B2_coeff_56
  recurrence2B2_coeff_57
  recurrence2B2_coeff_58
  recurrence2B2_coeff_59
  recurrence2B2_coeff_60
  recurrence2B2_coeff_61
  recurrence2B2_coeff_62
  recurrence2B2_coeff_63
  recurrence2B2_coeff_64
  recurrence2B2_coeff_65
  recurrence2B2_coeff_66
  recurrence2B2_coeff_67
  recurrence2B2_coeff_68
  recurrence2B2_coeff_69
  recurrence2B2_coeff_70
  recurrence2B2_coeff_71
  recurrence2B2_coeff_72
  recurrence2B2_coeff_73
  recurrence2B2_coeff_74
  recurrence2B2_coeff_75
  recurrence2B2_coeff_76
  recurrence2B2_coeff_77
  recurrence2B2_coeff_78
  recurrence2B2_coeff_79
  recurrence2B2_coeff_80
  recurrence2B2_coeff_81
  recurrence2B2_coeff_82
  recurrence2B2_coeff_83
  recurrence2B2_coeff_84
  recurrence2B2_coeff_85
  recurrence2B2_coeff_86
  recurrence2B2_coeff_87
  recurrence2B2_coeff_88
  recurrence2B2_coeff_89
  recurrence2B2_coeff_90
  recurrence2B2_coeff_91
  recurrence2B2_coeff_92
  recurrence2B2_coeff_93
  recurrence2B2_coeff_94
  recurrence2B2_coeff_95
  recurrence2B2_coeff_96
  recurrence2B2_coeff_97
  recurrence2B2_coeff_98
  recurrence2B2_coeff_99
  recurrence2B2_coeff_100
  recurrence2B2_coeff_101
  recurrence2B2_coeff_102
  recurrence2B2_coeff_103
  recurrence2B2_coeff_104
  recurrence2B2_coeff_105
  recurrence2B2_coeff_106
  recurrence2B2_coeff_107
  recurrence2B2_coeff_108
  recurrence2B2_coeff_109
  recurrence2B2_coeff_110
  recurrence2B2_coeff_111
  recurrence2B2_coeff_112
  recurrence2B2_coeff_113
  recurrence2B2_coeff_114
  recurrence2B2_coeff_115
  recurrence2B2_coeff_116
  recurrence2B2_coeff_117
  recurrence2B2_coeff_118
  recurrence2B2_coeff_119
  recurrence2B2_coeff_120
  recurrence2B2_coeff_121
  recurrence2B2_coeff_122
  recurrence2B2_coeff_123
  recurrence2B2_coeff_124
  recurrence2B2_coeff_125
  recurrence2B2_coeff_126
  recurrence2B2_coeff_127
  recurrence2B2_coeff_128
  recurrence2B2_coeff_129
  recurrence2B2_coeff_130
  recurrence2B2_coeff_131
  recurrence2B2_coeff_132
  recurrence2B2_coeff_133
  recurrence2B2_coeff_134
  recurrence2B2_coeff_135
  recurrence2B2_coeff_136
  recurrence2B2_coeff_137
  recurrence2B2_coeff_138
  recurrence2B2_coeff_139
  recurrence2B2_coeff_140
  recurrence2B2_coeff_141
  recurrence2B2_coeff_142
  recurrence2B2_coeff_143
  recurrence2B2_coeff_144
  recurrence2B2_coeff_145
  recurrence2B2_coeff_146
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

private theorem recurrence2Scalar3Shift_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (234 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_234 :
    recurrence2Scalar3Shift.coeff 234 =
      ((((6 * 10 ^ 70 +
        8045112059301782945780800692558710711581184574241101631341839838506014) * 10 ^ 70 +
        8520659286525495891774749200242768780454407723510359305779171034354904) * 10 ^ 70 +
        8818062023040775208207502741479610030940292063453615306095599884844573) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 5 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 14 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (235 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_235 :
    recurrence2Scalar3Shift.coeff 235 =
      -((((3 * 10 ^ 70 +
        5251186836675077885064813179853698429630606207730253459155540266402354) * 10 ^ 70 +
        5449933989482978960676790434869531104266916876637859964535052649333430) * 10 ^ 70 +
        3040933154233733680974824277701076221937308496909375563919550314594656) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 6 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 13 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (236 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_236 :
    recurrence2Scalar3Shift.coeff 236 =
      -(((984252315886437165465272901889807588565959753757488067490617742110750 * 10 ^ 70 +
        5202068715169340572201285517512607751227985388086345743876669654143370) * 10 ^ 70 +
        0488964344945328994826940919991387096201882053629932623520875289361931) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 7 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 12 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (237 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_237 :
    recurrence2Scalar3Shift.coeff 237 =
      ((((3 * 10 ^ 70 +
        6963161410301239299304872681862656343919442431848883708379592272340954) * 10 ^ 70 +
        4267467853709040147521367714865170854522681558997070000354969883922908) * 10 ^ 70 +
        8460609424631224088214293686543475547101383079867429296793565321744804) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 8 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 11 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (238 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_238 :
    recurrence2Scalar3Shift.coeff 238 =
      -((((6 * 10 ^ 70 +
        9072396539457650997187971182897199905956887441849893768295281520732350) * 10 ^ 70 +
        9036098248370291390822365854967136855367784572060583601440303000701027) * 10 ^ 70 +
        8317755256569570617387742539115807641209539170364893311137980278549862) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 9 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 10 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (239 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_239 :
    recurrence2Scalar3Shift.coeff 239 =
      ((((9 * 10 ^ 70 +
        4353331412208176487728233583895461914830613139315329121573860052358408) * 10 ^ 70 +
        6159019028746097716767956109065174709925524353965829468200616952092140) * 10 ^ 70 +
        5717788785070567213100829144143253473092864707940573361027736172427918) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 10 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 9 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (240 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_240 :
    recurrence2Scalar3Shift.coeff 240 =
      -((((11 * 10 ^ 70 +
        0923930921084437246309583676987449646378936985777748087313132041086381) * 10 ^ 70 +
        6572588182323750676847907371948660574399277318249191518483681501248444) * 10 ^ 70 +
        3189992927714045832742095880252022295203285215096157031780382970057863) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 11 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 8 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (241 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_241 :
    recurrence2Scalar3Shift.coeff 241 =
      ((((11 * 10 ^ 70 +
        8174640468439531275500698535259594564831135181134516118004254582247713) * 10 ^ 70 +
        0350579451028221591933414870317184185133623190898836601474297004074358) * 10 ^ 70 +
        6939334514467009851456096338407951867654769139474082725266220418962164) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 12 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 7 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (242 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_242 :
    recurrence2Scalar3Shift.coeff 242 =
      -((((11 * 10 ^ 70 +
        6717862858096654344588263454636186454072119356617169279007103285533187) * 10 ^ 70 +
        4942971211854935863241420939975459277959300058835856654058807617650324) * 10 ^ 70 +
        9057295381041927111175019887813911803171982034568858050493586755303695) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 13 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 6 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (243 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_243 :
    recurrence2Scalar3Shift.coeff 243 =
      ((((10 * 10 ^ 70 +
        8129057234213537802355232294393282881871845513245738775811943967386359) * 10 ^ 70 +
        1866036823986771538232463505412492029971086796948266629193612177886037) * 10 ^ 70 +
        7960040738799628032383304001791841827418613580917270093364611539460231) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 14 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 5 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (244 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_244 :
    recurrence2Scalar3Shift.coeff 244 =
      -((((9 * 10 ^ 70 +
        4559593539979105971679067176488783463900945285735970384263950695248621) * 10 ^ 70 +
        3966962651448622468687510433337958784570281747282111281259581753597952) * 10 ^ 70 +
        5463403967046370558207165322924264498923957374620146058007292067616394) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 15 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 4 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (245 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_245 :
    recurrence2Scalar3Shift.coeff 245 =
      ((((7 * 10 ^ 70 +
        8318044631045677750875763542469797164502820223912959584675843287245905) * 10 ^ 70 +
        3097533177715394353328045194933119549794669138192910826491098441768200) * 10 ^ 70 +
        9221632322922395161840116913453258334659447018954308575277708477838588) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 16 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 3 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (246 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_246 :
    recurrence2Scalar3Shift.coeff 246 =
      -((((6 * 10 ^ 70 +
        1506958671426531711499865630458447543265145300483161930269439805374414) * 10 ^ 70 +
        8440842368812900342040048790841922696106614149511324980620351895620844) * 10 ^ 70 +
        2263269325705196082084109789736369004434623749193487710849968458554087) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 17 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 2 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (247 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_247 :
    recurrence2Scalar3Shift.coeff 247 =
      ((((4 * 10 ^ 70 +
        5773335898575245331611528533098595660696095249079278732483465375001383) * 10 ^ 70 +
        3727656572452565357054868684321081972594711995078232888784673006958584) * 10 ^ 70 +
        2681968465656518106530512335977479382681397487857414629300949144634822) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 18 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 1 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (248 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_248 :
    recurrence2Scalar3Shift.coeff 248 =
      -((((3 * 10 ^ 70 +
        2194236926733089289495745494197106512548505723185807673865883664558868) * 10 ^ 70 +
        7689943911644543887726056502026791502467228140169446396369794152177863) * 10 ^ 70 +
        9072586284494718683411935540378462272158844150796757128914131873098168) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 19 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (249 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_249 :
    recurrence2Scalar3Shift.coeff 249 =
      ((((2 * 10 ^ 70 +
        1285363256010973058383140410945403464926806384951216589266513157671900) * 10 ^ 70 +
        0666148262442981777625470300041432060275988889978427958161744269143774) * 10 ^ 70 +
        5265862028066264395391507486466602444921785188451364687025831689414764) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 20 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 31 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (250 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_250 :
    recurrence2Scalar3Shift.coeff 250 =
      -((((1 * 10 ^ 70 +
        3097892661814497713285262287490107815660782258234770001150623753093058) * 10 ^ 70 +
        5967321878347539983074509457215553394945623137879911638487715526778832) * 10 ^ 70 +
        1323003940529454134571513053499959107752863789061232534727592280162596) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 21 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 30 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (251 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_251 :
    recurrence2Scalar3Shift.coeff 251 =
      (((7360224859718040417402655663425804284306570643082329452095655459692366 * 10 ^ 70 +
        6497884352461941395658075584646840837521508282983454152325469314733933) * 10 ^ 70 +
        8126343533578355334508000651674390630187397199833956124414261377070789) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 22 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 29 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (252 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_252 :
    recurrence2Scalar3Shift.coeff 252 =
      -(((3624957825526599451431771535649959566173903707574013306075113029799292 * 10 ^ 70 +
        2580241263299541169678615973961616724717419440574894569180251750408672) * 10 ^ 70 +
        7159893312326737544414159828823660125178806588343610196869244555798778) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 23 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 28 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (253 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_253 :
    recurrence2Scalar3Shift.coeff 253 =
      (((1392888845477761998976544713546866413719294633855691071633021945153591 * 10 ^ 70 +
        0208347392063773286153975511803929087542774307512638318804872519218409) * 10 ^ 70 +
        2138472311569613670030100087539589497799169805836711412409500649875216) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 24 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 27 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (254 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_254 :
    recurrence2Scalar3Shift.coeff 254 =
      -(((199893631578718522613034946648294576563547879190859459062639050843008 * 10 ^ 70 +
        3417025723397558525480151907266355802575290651014386891827652515398397) * 10 ^ 70 +
        8960012038931590285114301307495211073893705850163130121288304355381592) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 25 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 26 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (255 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_255 :
    recurrence2Scalar3Shift.coeff 255 =
      -(((335069410781554841584343714977542234950644045131385392377908981566794 * 10 ^ 70 +
        9989534184391702339633320603375998733662476589312614535838316573789320) * 10 ^ 70 +
        2511207740010961577353290034011587155462643616475761814513947761925617) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 26 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 25 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (256 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_256 :
    recurrence2Scalar3Shift.coeff 256 =
      (((494250009998212231706990034622879093975352592580998828976097989031774 * 10 ^ 70 +
        0673316659607892043555148874154810227377725728452018868279220957306278) * 10 ^ 70 +
        6089995855997920932660201596179830217288867223242849518109513041632378) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 27 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 24 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (257 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_257 :
    recurrence2Scalar3Shift.coeff 257 =
      -(((467344076984016909215660691612052339201419348116219163204089072078001 * 10 ^ 70 +
        9258899321271034131121148837295496295040795252148709397754906307514480) * 10 ^ 70 +
        4228945999837492975085774415617559482424292265009228821312567689656423) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 28 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 23 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (258 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_258 :
    recurrence2Scalar3Shift.coeff 258 =
      (((369276234898076585446257959226395237216526671389265382563085627207147 * 10 ^ 70 +
        5345410757683098587917550165821808827291758824195617269554531030987643) * 10 ^ 70 +
        9870230700816445995463126641424190238382276469000917932033356141784564) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 29 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 22 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (259 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_259 :
    recurrence2Scalar3Shift.coeff 259 =
      -(((261316781596460011421887814291232272715811947005139684063427600949727 * 10 ^ 70 +
        3856920586473306548025595918293139271346580834846310325061971459242374) * 10 ^ 70 +
        9622164551836938980967811776648379710298694147652412667637188231508063) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 30 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 21 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (260 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_260 :
    recurrence2Scalar3Shift.coeff 260 =
      (((170321424225756766466611502444353512136477469813944023499247451372974 * 10 ^ 70 +
        8820743660107055081602232114749259648737306171431310011552305861571731) * 10 ^ 70 +
        1335315738975679790359944180743487075160639055884253501372709638035144) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 31 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 20 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (261 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_261 :
    recurrence2Scalar3Shift.coeff 261 =
      -(((103646902410212983992206825950174210730084065637612008527997830718464 * 10 ^ 70 +
        3535752693528520527029331072655792735635997022657401558116528770326358) * 10 ^ 70 +
        9736875138625978434843764386578201630314159531313450026590134027853202) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 32 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 19 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (262 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_262 :
    recurrence2Scalar3Shift.coeff 262 =
      (((59297558041482507808099918298639257394377847646181755717358564416758 * 10 ^ 70 +
        3904574044954808157391637433808366041070399952348734407448780257284361) * 10 ^ 70 +
        1478987875120665723473856803116535009703740113081178822171605972846598) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 33 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 18 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (263 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_263 :
    recurrence2Scalar3Shift.coeff 263 =
      -(((31994520742208810021337784450820105089111286458391130181207449221784 * 10 ^ 70 +
        5489961893990492759501410536706195203245437219803112675898647218520010) * 10 ^ 70 +
        1219844117910104713476337933226459435378944900875342378838986873855060) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 34 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 17 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (264 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_264 :
    recurrence2Scalar3Shift.coeff 264 =
      (((16287897578842022291783637759802897905549022013695655596584546463002 * 10 ^ 70 +
        5328717529721306833318807642801189631945269241027164512856303703218541) * 10 ^ 70 +
        5481156193249220171953146455181912619641743999787071255013183922394052) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 35 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 16 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (265 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_265 :
    recurrence2Scalar3Shift.coeff 265 =
      -(((7807326802297351195630673231149276767836519066037224975947649281772 * 10 ^ 70 +
        1103065408295855748673119391301120436699896863127339434741061711361556) * 10 ^ 70 +
        6949968591200129453837454015279662326064000650762366199477825749592534) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 36 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 15 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
