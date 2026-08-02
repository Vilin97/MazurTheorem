/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (266 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_266 :
    recurrence2Scalar3Shift.coeff 266 =
      (((3505339372462333578743221398221915899774424955446695345439438557086 * 10 ^ 70 +
        2287663813650478725402951423861817997043824860279743838332104528763404) * 10 ^ 70 +
        5679483295191567061231971977190123921293338090340136680661869927984690) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 37 +
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
    rw [show 134 = 14 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (267 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_267 :
    recurrence2Scalar3Shift.coeff 267 =
      -(((1459307117436888036509478271413065576551376368744125075919786811573 * 10 ^ 70 +
        4395618544489239181168992970576831314204425148608551049605502101029152) * 10 ^ 70 +
        0494828631779175338841997842405734564157485423831954069903827913093713) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 38 +
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
    rw [show 134 = 13 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (268 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_268 :
    recurrence2Scalar3Shift.coeff 268 =
      (((552278004072104579299780511196293996171784831573133653741505037019 * 10 ^ 70 +
        3598099215781005482575296436946440396405118059855638111209470009519846) * 10 ^ 70 +
        4147573774758095289666147567088848726442994366088063396329799529225833) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 39 +
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
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (269 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_269 :
    recurrence2Scalar3Shift.coeff 269 =
      -(((181911175864383803302729650273254782614436619085328080891076105096 * 10 ^ 70 +
        7623734409547428715777611045497416115188898120742001197788565528092578) * 10 ^ 70 +
        0766560530445795008967822842947865347110520314091042842343967000920616) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 40 +
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
    rw [show 134 = 11 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (270 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_270 :
    recurrence2Scalar3Shift.coeff 270 =
      (((45951459109897340177647976607415507818507900395587883792675508796 * 10 ^ 70 +
        6785701832824707155544563554939960795264944378831022397284767722501003) * 10 ^ 70 +
        9492505406020085200875389935734792252210688483856966505272718645132741) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 41 +
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
    rw [show 134 = 10 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (271 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_271 :
    recurrence2Scalar3Shift.coeff 271 =
      -(((3571716050517223792554121611708622160500147256256463743996850952 * 10 ^ 70 +
        1403206535394374819810343690832428724055574571365277343424189358389992) * 10 ^ 70 +
        5145139347165870014698690809184991870070171852566894608767034467345773) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 42 +
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
    rw [show 134 = 9 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (272 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_272 :
    recurrence2Scalar3Shift.coeff 272 =
      -(((5682390380080016414472184816352086704264959799184902040064058883 * 10 ^ 70 +
        6667068557797608531478121240506362543346123293144283832961517015284496) * 10 ^ 70 +
        5195840324207505265218743362862355683772263261502536692591867808904000) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 43 +
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
    rw [show 134 = 8 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (273 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_273 :
    recurrence2Scalar3Shift.coeff 273 =
      (((5314765944633047436276232672208491324595086473252079073806908415 * 10 ^ 70 +
        6457174436198877830364711807688005219631848778244125845756006275459896) * 10 ^ 70 +
        3547679795220191474044540409259267050286289985965643714535459709135183) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 44 +
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
    rw [show 134 = 7 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (274 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_274 :
    recurrence2Scalar3Shift.coeff 274 =
      -(((3286269797971797284075338352197413124651400150830953344827152255 * 10 ^ 70 +
        0916855522386920265344755756298209792235336671949598520153349238860702) * 10 ^ 70 +
        5557861410060228194888428892173417226927020420266838099965022813515897) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 45 +
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
    rw [show 134 = 6 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (275 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_275 :
    recurrence2Scalar3Shift.coeff 275 =
      (((1701250794730564997813335618317532239125456617194593585222156627 * 10 ^ 70 +
        9088591896896761483248261770242822702438489973698015528278629981939336) * 10 ^ 70 +
        1475875027904445745774125746489919587107063082414275737699641999634251) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 46 +
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
    rw [show 134 = 5 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (276 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_276 :
    recurrence2Scalar3Shift.coeff 276 =
      -(((785948971418392467623657474688541718714566376632100602381789848 * 10 ^ 70 +
        4697739746850757865744518398069215514943070255260839554680947675111889) * 10 ^ 70 +
        7801016909133435472136306717847236738279539961091096169775785365604030) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 47 +
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
    rw [show 134 = 4 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (277 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_277 :
    recurrence2Scalar3Shift.coeff 277 =
      (((332362068553419959843977611969051368413570631507887589539989541 * 10 ^ 70 +
        0357658568534158485734900139240713639608737918527348497497328800783580) * 10 ^ 70 +
        9228361842837895021706928914151796417442461440305438761867261398872485) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 48 +
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
    rw [show 134 = 3 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (278 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_278 :
    recurrence2Scalar3Shift.coeff 278 =
      -(((130106301592050450384948583059391378881279737951844802144025673 * 10 ^ 70 +
        5443955950927806915584792348599357127321655219300180558277830379052347) * 10 ^ 70 +
        9473379346596196004843908736295354169809085129298421124666094229123336) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 49 +
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
    rw [show 134 = 2 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (279 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_279 :
    recurrence2Scalar3Shift.coeff 279 =
      (((47339231231202666032397754823226129881442078246978221347725075 * 10 ^ 70 +
        2183153221539783582875034896099702807520056063050258485569183810906837) * 10 ^ 70 +
        8671684137827171227382065909155409295764225802006008913928922580722423) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 50 +
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
    rw [show 134 = 1 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (280 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_280 :
    recurrence2Scalar3Shift.coeff 280 =
      -(((15994220256212456773328539073117412736245596157154215171517368 * 10 ^ 70 +
        2205822019136035250975778329307653938666297385317721655618523072214412) * 10 ^ 70 +
        2752499433131088199592297160023184014034919853118307051010485138504533) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 51 +
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
  rw [recurrence2Scalar3Shift_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (281 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_281 :
    recurrence2Scalar3Shift.coeff 281 =
      (((4987166493356664970667303446753175801078031062559467757192338 * 10 ^ 70 +
        0132873122940358483311227030812780494702541012431181524771007654068027) * 10 ^ 70 +
        1729701178143529518741055446358570629403249961815437471634693581448900) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 52 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 31 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (282 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_282 :
    recurrence2Scalar3Shift.coeff 282 =
      -(((1415248148793833299453068269705187339345692650544806288154514 * 10 ^ 70 +
        4464407172151439605311566843709119753161391310732572828736039468526006) * 10 ^ 70 +
        3946482369676806145031793771886383423904068044218418353502631624453959) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 53 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 30 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (283 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_283 :
    recurrence2Scalar3Shift.coeff 283 =
      (((354681302057736508026121144546970136965626243378440999240810 * 10 ^ 70 +
        4606411271391924332248764648849310673172347144553437599754904156377794) * 10 ^ 70 +
        7128162561454530920622424845121678389900666495745655129108775003053003) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 54 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 29 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (284 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_284 :
    recurrence2Scalar3Shift.coeff 284 =
      -(((72745021253562085893749787969797045986961463263783722854071 * 10 ^ 70 +
        0305112533820771228216651526137974518204426011811876159842442459971457) * 10 ^ 70 +
        4809751066758116394849014201205669099140115916067624269545425569009591) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 55 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 28 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (285 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_285 :
    recurrence2Scalar3Shift.coeff 285 =
      (((8958758865263356365487773097672553304214935250300494963735 * 10 ^ 70 +
        2840161669889361932056650854522540411805588247031801893269073942799933) * 10 ^ 70 +
        3939280268449561528953876643790573414886903237036536023726073115451001) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 56 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 27 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (286 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_286 :
    recurrence2Scalar3Shift.coeff 286 =
      (((1506809491816607468863047584109784426716470349979090405007 * 10 ^ 70 +
        7662780260454374378083552551727774257050480769874773627148908337088030) * 10 ^ 70 +
        3658390286326817172190474268973191057822286472233763888177129498855557) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 57 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (287 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_287 :
    recurrence2Scalar3Shift.coeff 287 =
      -(((1635017140476793296061844032144318022650388001551253163087 * 10 ^ 70 +
        8009602327962869745470455632321633853551040429401652116999927885874346) * 10 ^ 70 +
        4691930746062299648398664626239395048477944499371635110023254737776441) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 58 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 25 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (288 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_288 :
    recurrence2Scalar3Shift.coeff 288 =
      (((772933188309064531665444687581252069394429553878111741048 * 10 ^ 70 +
        8516300612447828041903069595720435399419397571017328178935746324244020) * 10 ^ 70 +
        9179525360208139738618468436508472612163252495578718563929102063667013) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 59 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 24 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (289 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_289 :
    recurrence2Scalar3Shift.coeff 289 =
      -(((284068338514117184363889432760921170042243547435692167864 * 10 ^ 70 +
        5132111379801217408479133051489362246854400297466943334182019122273591) * 10 ^ 70 +
        3124199620685667593998769645440326367641404836837629927944436407244794) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 60 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 23 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (290 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_290 :
    recurrence2Scalar3Shift.coeff 290 =
      (((89807497003879435256649045682054559030560995527208469612 * 10 ^ 70 +
        4121548432047628396883970185085370415203586707161893805669153799657510) * 10 ^ 70 +
        4560608052337100305839679506922235430787906542370014266174520311457531) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 61 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 22 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (291 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_291 :
    recurrence2Scalar3Shift.coeff 291 =
      -(((25240018187811963325296028999183600634032227604610820628 * 10 ^ 70 +
        3140749187443658515160150553087031216313704580108114204831861642926900) * 10 ^ 70 +
        0333644650254472282375001056074362939457574151547979336182102562422807) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 62 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 21 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (292 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_292 :
    recurrence2Scalar3Shift.coeff 292 =
      (((6368444382621510494352939273350881146996789417325484658 * 10 ^ 70 +
        6777934224181886765128447295168681190776588479861356025072417538289433) * 10 ^ 70 +
        3811126854808458966213966272536505935222921847035140022532256545438295) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 63 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 20 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (293 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_293 :
    recurrence2Scalar3Shift.coeff 293 =
      -(((1437249165000131132368464910378248571877606191760524243 * 10 ^ 70 +
        8872244906862878410727544334500160154123515392572061808526513176846736) * 10 ^ 70 +
        1605229984336266042116995483019215581995604628105463290448749647166481) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 64 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 19 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (294 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_294 :
    recurrence2Scalar3Shift.coeff 294 =
      (((284655752157619235908334997096608047343575193839640025 * 10 ^ 70 +
        4820318854605200394084749324898925990589877814888465567530614827150474) * 10 ^ 70 +
        7341655504340841710032406515919965520386816320457425029278057164779748) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 65 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 18 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (295 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_295 :
    recurrence2Scalar3Shift.coeff 295 =
      -(((47018228335198997470682102849301328700180419932147450 * 10 ^ 70 +
        8493070961305980589665293066804281274522941184378687852205372635126816) * 10 ^ 70 +
        9805679538134488842192602048892886832872475650075314405257511130831328) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 66 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 17 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (296 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_296 :
    recurrence2Scalar3Shift.coeff 296 =
      (((5472876286869920591916675397156778264701250672310253 * 10 ^ 70 +
        8273045606274921927469591055266735387006994488056421540517363127986821) * 10 ^ 70 +
        1313163438784190065027448868225664696899465190392435857449660499567905) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 67 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (297 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_297 :
    recurrence2Scalar3Shift.coeff 297 =
      -(((5595510924450127957217287274425747541780246905258 * 10 ^ 70 +
        6317529346834917510015717425625525012242191586038171274370653068070752) * 10 ^ 70 +
        5281953007583094180852153409389826949188523044566409138939781841901560) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 68 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 15 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (298 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_298 :
    recurrence2Scalar3Shift.coeff 298 =
      -(((239953614802551106702405134845032913621982985325463 * 10 ^ 70 +
        3376663499586926647354008636346207587165939243300709553806116595178788) * 10 ^ 70 +
        6048328459413340204147664753953881888040598729757946527597482866281851) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 69 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 14 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (299 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_299 :
    recurrence2Scalar3Shift.coeff 299 =
      (((91031807695649233122014570432927561621745593832438 * 10 ^ 70 +
        4373662020931014897475328311506803271186745047917910026997060938264616) * 10 ^ 70 +
        5827314859130264031626777271148621388224832953743579971629520499560156) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 70 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 13 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (300 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_300 :
    recurrence2Scalar3Shift.coeff 300 =
      -(((23898764154797113251399357905195646853363849447805 * 10 ^ 70 +
        1639021666097075691941750090293036991890426599221885815010965722007163) * 10 ^ 70 +
        1682338733124183112007619739533920431023544309846003953182637180856632) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 71 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (301 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_301 :
    recurrence2Scalar3Shift.coeff 301 =
      (((5096819024125284467421690692809739429571429805732 * 10 ^ 70 +
        2128623081879374657337679965546397560832053083082355784096088352335600) * 10 ^ 70 +
        6028829104040986660801736071772705276053171024143695572642004616267400) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 72 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 11 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (302 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_302 :
    recurrence2Scalar3Shift.coeff 302 =
      -(((914736044970298857755319479562490027087103909836 * 10 ^ 70 +
        3034588106155218253398012868527308923380480524299785935086409778625413) * 10 ^ 70 +
        8859214408701936851290906695821499380175354225607596227045461884060970) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 73 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 10 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (303 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_303 :
    recurrence2Scalar3Shift.coeff 303 =
      (((136641576936893146959594814371194155893667841423 * 10 ^ 70 +
        1470904995600545701726500592217765813139141133435285409579179404133801) * 10 ^ 70 +
        8630692160229910478982048341092214309018492192027253387661064009753068) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 74 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (304 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_304 :
    recurrence2Scalar3Shift.coeff 304 =
      -(((15821314632747899021161093010690305768491759541 * 10 ^ 70 +
        5229234073179160786652211435251214529041691111229271720760391929168419) * 10 ^ 70 +
        9216970578752971164903835731416051254290677147104737830794229579612434) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 75 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 8 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (305 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_305 :
    recurrence2Scalar3Shift.coeff 305 =
      (((1014846042798991912214209860223199286220082255 * 10 ^ 70 +
        8902004701092955905843038931665893064628150902208595957632450861494172) * 10 ^ 70 +
        7325660408827383695109707497395018407874838659173242362301201232556239) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 76 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 7 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (306 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_306 :
    recurrence2Scalar3Shift.coeff 306 =
      (((108262072426078001072826329669732993262656271 * 10 ^ 70 +
        5541618802744472444985231206107662954101972796005282896592347392759218) * 10 ^ 70 +
        1406767010935322352508340023463077196805090560346643588247414116021574) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 77 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 6 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (307 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_307 :
    recurrence2Scalar3Shift.coeff 307 =
      -(((53301064334539152553313579593822018554879913 * 10 ^ 70 +
        8282635222363399481214830901285571751493719195177500685089753913018216) * 10 ^ 70 +
        1177580998142761649200866469423723943417257042066953849357645005475940) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 78 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 5 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (308 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_308 :
    recurrence2Scalar3Shift.coeff 308 =
      (((11588432056410276016394875774461007718251541 * 10 ^ 70 +
        7212127660254770438395770628854060628779733742521798472298711552614938) * 10 ^ 70 +
        1315741633180302666409125783393912581113185719469942629117310798216615) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 79 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 4 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (309 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_309 :
    recurrence2Scalar3Shift.coeff 309 =
      -(((1822884261106759236142571834499847887865415 * 10 ^ 70 +
        2243884793130288665864943044948135104402659668230607770383689578958387) * 10 ^ 70 +
        6660821908393052796548205464436917474176783332418896698829956425405531) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 80 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 3 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (310 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_310 :
    recurrence2Scalar3Shift.coeff 310 =
      (((218368209470656221056622522055351831723996 * 10 ^ 70 +
        4262037077841531627057268721121796552796332628878158686374609145462500) * 10 ^ 70 +
        5944126244646063318059476381193898668575825761202883282591198631928566) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 81 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 2 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (311 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_311 :
    recurrence2Scalar3Shift.coeff 311 =
      -(((18028604189167337040831334855582858755950 * 10 ^ 70 +
        6453181908077756248491769028551976504203526444447363547539373692410037) * 10 ^ 70 +
        9311789772774767881284818355129364240098934741759706421031304566770474) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 82 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 1 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (312 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_312 :
    recurrence2Scalar3Shift.coeff 312 =
      (((367261709739049883912436760977453702631 * 10 ^ 70 +
        2563762428673099573899881651810890752639033632534764854390362694951024) * 10 ^ 70 +
        3232645052840193572579071242060365074278698752482678628703774791550435) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 83 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (313 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_313 :
    recurrence2Scalar3Shift.coeff 313 =
      (((202101879713460729378091813889441061324 * 10 ^ 70 +
        9282213494739765172996805780864368249611690622211309914347088689405958) * 10 ^ 70 +
        4752873225625932136152911351747721584518459914836101062867944753539764) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 84 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 31 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (314 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_314 :
    recurrence2Scalar3Shift.coeff 314 =
      -(((46732814658551736694930577508032397827 * 10 ^ 70 +
        2158374676349228110671162645531561068094141570762903394600170183728280) * 10 ^ 70 +
        9314475113039279811987371854679864908115891321124153125435415528390022) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 85 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 30 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (315 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_315 :
    recurrence2Scalar3Shift.coeff 315 =
      (((6467219982354390208481968386769752478 * 10 ^ 70 +
        5394590238602251839787034260714099329853143283242106985599366507734382) * 10 ^ 70 +
        2959937588513398598522460289484928496438110118810474095296671577845953) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 86 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 29 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (316 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_316 :
    recurrence2Scalar3Shift.coeff 316 =
      -(((636981838681375016228352252358057182 * 10 ^ 70 +
        5696951993615077396083962039552834425833981037706747360212501911188463) * 10 ^ 70 +
        1188321838357165747571251434670589124330678504715350893942399542528309) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 87 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 28 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (317 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_317 :
    recurrence2Scalar3Shift.coeff 317 =
      (((40873258610628590943332086257414705 * 10 ^ 70 +
        1390806687759443389222788762314174529028140633785903880073821398721622) * 10 ^ 70 +
        0798285556410255205197156877368900523139374236274318221135667593408084) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 88 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 27 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (318 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_318 :
    recurrence2Scalar3Shift.coeff 318 =
      -(((398069549374174767139478476067331 * 10 ^ 70 +
        3297358641510058743683729706634080753487859280221974353139377501722721) * 10 ^ 70 +
        1466009925800745182889650512900684903729278322397723426509427969152557) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 89 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 26 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (319 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_319 :
    recurrence2Scalar3Shift.coeff 319 =
      -(((315869612680423027888739389081269 * 10 ^ 70 +
        4405642786024700860154867039092093255864714696519005206107236245590488) * 10 ^ 70 +
        7548536709831783673034450521626904644261388563611750715992075356428369) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 90 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 25 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (320 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_320 :
    recurrence2Scalar3Shift.coeff 320 =
      (((51259158690130321894850995325899 * 10 ^ 70 +
        2468783260239492925724296140915838404028326155112225835746544186162366) * 10 ^ 70 +
        5248302171718683088523586537537471133035859213440255773029301487964101) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 91 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 24 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (321 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_321 :
    recurrence2Scalar3Shift.coeff 321 =
      -(((4952760419246593641383599979357 * 10 ^ 70 +
        6846925312305552934784878500452599564234309485302190806829440313446926) * 10 ^ 70 +
        2866493612372266681395670223710479811979568854376411886883892172819478) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 92 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 23 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (322 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_322 :
    recurrence2Scalar3Shift.coeff 322 =
      (((321527027857941854138989077303 * 10 ^ 70 +
        1273334297738246090278960832550967332613115819119928251607075276663966) * 10 ^ 70 +
        7534184404694164282756476925428256463415403642631750945780799751059442) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 93 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 22 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (323 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_323 :
    recurrence2Scalar3Shift.coeff 323 =
      -(((11061259688620477869926207105 * 10 ^ 70 +
        8289142389862590826565346154263387421400468442006726455618165945672841) * 10 ^ 70 +
        4641767162770408794475637543468507868276897776823309577380800128850721) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 94 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 21 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (324 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_324 :
    recurrence2Scalar3Shift.coeff 324 =
      -(((369435669482380152851931893 * 10 ^ 70 +
        3026972397287633927550305040526357865050044073074305270812872567259865) * 10 ^ 70 +
        9357281627248237078012683081281084444923908834813865538476364073846095) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 95 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 20 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (325 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_325 :
    recurrence2Scalar3Shift.coeff 325 =
      (((88675754914654568680606328 * 10 ^ 70 +
        8016799464780418963653001154915712424337310955607756898707510102675234) * 10 ^ 70 +
        2573599446362874172981030506066057711450829314988542860986596528147510) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 96 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 19 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (326 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_326 :
    recurrence2Scalar3Shift.coeff 326 =
      -(((7260745550125830388303648 * 10 ^ 70 +
        8811424974968258593864655427623588856410115355974914379570475086456292) * 10 ^ 70 +
        9221352921738046212009237987612527488833191190170110844188936817589784) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 97 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 18 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (327 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_327 :
    recurrence2Scalar3Shift.coeff 327 =
      (((356427983171439196716601 * 10 ^ 70 +
        1355558604818157615450511608444729654590119124981237344435471156849873) * 10 ^ 70 +
        6768992614223563915634664912755870953123643863719582460097555924812329) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 98 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 17 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (328 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_328 :
    recurrence2Scalar3Shift.coeff 328 =
      -(((8500731867432920524017 * 10 ^ 70 +
        2163207452612863077777908803167380716253246678855356477681842171251842) * 10 ^ 70 +
        4365678766902651366217202374410248447999958826961282390983502900807722) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 99 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 16 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (329 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_329 :
    recurrence2Scalar3Shift.coeff 329 =
      -(((227654867472782899381 * 10 ^ 70 +
        1108652810125951596190039353104901023886936930154441407210031309870382) * 10 ^ 70 +
        7065308319138120651898314570509375136421686524691069546954595746836015) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 100 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 15 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (330 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_330 :
    recurrence2Scalar3Shift.coeff 330 =
      (((32193326328317321431 * 10 ^ 70 +
        8314597259696478245163884909569741194915965593934616997506621440817237) * 10 ^ 70 +
        0317689700140931517851968815633936166813793939598562333270050779663979) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 101 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 14 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (331 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_331 :
    recurrence2Scalar3Shift.coeff 331 =
      -(((1522419035547277143 * 10 ^ 70 +
        9120203981289647394957645224268192199241881827308576955665463784477787) * 10 ^ 70 +
        5598058043073761419315647817677296569429307681696117737008162334663773) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 102 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 13 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (332 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_332 :
    recurrence2Scalar3Shift.coeff 332 =
      (((35338316776429816 * 10 ^ 70 +
        8918081041052995139774874453293979272738602542028812091457846737275728) * 10 ^ 70 +
        7541317979101159257736434767528411614690886104973892369667999934290277) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 103 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 12 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (333 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_333 :
    recurrence2Scalar3Shift.coeff 333 =
      (((82936043550752 * 10 ^ 70 +
        8259196518862366003424057584577156798705365459864710287754087191365355) * 10 ^ 70 +
        1900108990292771863071184368019820248508885742401371430615680152946385) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 104 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 11 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (334 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_334 :
    recurrence2Scalar3Shift.coeff 334 =
      -(((35059301771352 * 10 ^ 70 +
        4950674648106323375496334187492851025155712264337316105281665154232640) * 10 ^ 70 +
        3433160686925053170313291735790565812483088886183450849166505875208925) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 105 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 10 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (335 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_335 :
    recurrence2Scalar3Shift.coeff 335 =
      (((1136712399084 * 10 ^ 70 +
        8202985952212429392296325601449831801177290838841695146247249145814385) * 10 ^ 70 +
        4344623470617119543721388193477972144534597462648953279530979838029331) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 106 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 9 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (336 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_336 :
    recurrence2Scalar3Shift.coeff 336 =
      -(((13247371014 * 10 ^ 70 +
        8308539211999096722388485415962410364185872180514673753624826899695535) * 10 ^ 70 +
        6985533458148373575856872063142775546233871476752823882682530067146651) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 107 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 8 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (337 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_337 :
    recurrence2Scalar3Shift.coeff 337 =
      -(((171251846 * 10 ^ 70 +
        0058707341757629495054623911498632908092134146569117089231304209554615) * 10 ^ 70 +
        5941924208081933784775686390960777820656383733673613220073438625220822) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 108 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 7 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (338 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_338 :
    recurrence2Scalar3Shift.coeff 338 =
      (((7729130 * 10 ^ 70 +
        6832879553047241271067340599446401415965589416913378221228515693782507) * 10 ^ 70 +
        8909107385958603360722874737238722685752069121743241937981853313274324) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 109 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 6 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (339 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_339 :
    recurrence2Scalar3Shift.coeff 339 =
      -(((79467 * 10 ^ 70 +
        2281802734705075892003668072950578076954424970453013313294235048488450) * 10 ^ 70 +
        4395690913695422220199081335852946141454146000772407873609878294132236) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 110 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 5 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (340 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_340 :
    recurrence2Scalar3Shift.coeff 340 =
      -(((466 * 10 ^ 70 +
        4192822789109021217301851965792944087098548800274137403540648157776335) * 10 ^ 70 +
        4563027060934648235009782246294518642705732782008959115108461183101211) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 111 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 4 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (341 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_341 :
    recurrence2Scalar3Shift.coeff 341 =
      (((15 * 10 ^ 70 +
        7644598980336030532757602447541890761383613873306135639365217265448312) * 10 ^ 70 +
        6799391734214307022192141413059846821452046111464051111281872643190236) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 112 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 3 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (342 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_342 :
    recurrence2Scalar3Shift.coeff 342 =
      -((627626893075892454386287886836668899936096622397991275063461847421196 * 10 ^ 70 +
        6454577332777221710015989226024063462470695218096869255278376080024819) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 113 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 2 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (343 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_343 :
    recurrence2Scalar3Shift.coeff 343 =
      -((9930499660016114127638051725177304927415096746931535857697046224674 * 10 ^ 70 +
        1356677144963770492598277625363244658674582967419888403805748315475559) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 114 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 1 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (344 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_344 :
    recurrence2Scalar3Shift.coeff 344 =
      ((81826728700567318714040865446037735878136832542297240542638701158 * 10 ^ 70 +
        2807471221351396070560066258490280574202332770110168739958257966099845) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 115 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (345 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_345 :
    recurrence2Scalar3Shift.coeff 345 =
      ((257301846929008225471371544164409318792275984656306618155901664 * 10 ^ 70 +
        4550066869923006596881721199338682053527518167638310547766548320008541) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 116 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 31 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (346 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_346 :
    recurrence2Scalar3Shift.coeff 346 =
      -((3889692393618105503261552997279898198386528612155066406722597 * 10 ^ 70 +
        7693397951904969470419032676373995610746940461330205348873839513556655) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 117 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 30 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (347 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_347 :
    recurrence2Scalar3Shift.coeff 347 =
      -((740989285024878836121972638973176078254135445440231290242 * 10 ^ 70 +
        2861482076530659104164346878315813765031244056657751622108704315531316) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 118 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 29 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (348 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_348 :
    recurrence2Scalar3Shift.coeff 348 =
      ((96543156598210164959306376260356299965513643544875411100 * 10 ^ 70 +
        7479247137229142884484108844962851190008129305776677889612155423853661) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 119 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 28 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (349 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_349 :
    recurrence2Scalar3Shift.coeff 349 =
      -((117329047297662773853458320093103492519261978741542481 * 10 ^ 70 +
        2124895726658445545673840365825765160183476775091250050414022597989514) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 120 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 27 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (350 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_350 :
    recurrence2Scalar3Shift.coeff 350 =
      -((1308762101161586506729729642070179299513105417560564 * 10 ^ 70 +
        9139033331594766144437161435722703992529313876594439203128841186741489) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 121 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 26 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (351 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_351 :
    recurrence2Scalar3Shift.coeff 351 =
      ((2969055682104249693033070283909213065285837969325 * 10 ^ 70 +
        3375776272007091730558483455437939107102155080623410248278471689598223) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 122 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 25 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (352 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_352 :
    recurrence2Scalar3Shift.coeff 352 =
      ((8621666411570524824476412825759622122946989636 * 10 ^ 70 +
        5420877912349702067347227654019087734004423696389500428236972240822044) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 123 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 24 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (353 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_353 :
    recurrence2Scalar3Shift.coeff 353 =
      -((31943216475720628569317190242591194848812386 * 10 ^ 70 +
        2196373438556348006578685190548429672736651147459732028848500123264736) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 124 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 23 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (354 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_354 :
    recurrence2Scalar3Shift.coeff 354 =
      -((9619462725666532684998940447891910282728 * 10 ^ 70 +
        0199653221911724033690506931440753315703795116908561669089088199855243) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 125 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 22 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (355 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_355 :
    recurrence2Scalar3Shift.coeff 355 =
      ((149364870373557463259330379543222616751 * 10 ^ 70 +
        7723818465477456647383307972384702245162566833831079936615132711976765) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 126 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 21 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (356 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_356 :
    recurrence2Scalar3Shift.coeff 356 =
      -((154717701436839856146371287802271709 * 10 ^ 70 +
        1536783776051650527281760246654030936687451148034203772965148089412056) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 127 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 20 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (357 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_357 :
    recurrence2Scalar3Shift.coeff 357 =
      -((153945028770103129077717567469866 * 10 ^ 70 +
        2100203697508895887441526848438226328432919045287365977274681632426877) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 128 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 19 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (358 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_358 :
    recurrence2Scalar3Shift.coeff 358 =
      ((417990921122235296519761732630 * 10 ^ 70 +
        0884748575913449004617692563562344812670556925242444438558294642939863) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 129 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 18 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (359 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_359 :
    recurrence2Scalar3Shift.coeff 359 =
      -((284474063529363702207430955 * 10 ^ 70 +
        3290641655238165460358128517580832771568586381193365621498594407387534) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 130 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 17 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (360 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_360 :
    recurrence2Scalar3Shift.coeff 360 =
      ((20142920343341738292875 * 10 ^ 70 +
        0991048049413455595692938797710041707775497587375658806592795169062073) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 131 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 16 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (361 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_361 :
    recurrence2Scalar3Shift.coeff 361 =
      ((59883243616274239521 * 10 ^ 70 +
        6586506244118301054368294398929001493128977325780572736350802801938219) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 132 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 15 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (362 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_362 :
    recurrence2Scalar3Shift.coeff 362 =
      -((26999596876736381 * 10 ^ 70 +
        6330668664512368831426845672176168766310745696891890530854996402178125) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 133 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 14 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (363 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_363 :
    recurrence2Scalar3Shift.coeff 363 =
      ((4182527216633 * 10 ^ 70 +
        9586209700382871870430823030626200207211332330611846469443862095902286) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 134 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 13 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (364 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_364 :
    recurrence2Scalar3Shift.coeff 364 =
      -((140237945 * 10 ^ 70 +
        1849784473461775035477856139875735881958807820661374535752697602049867) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 135 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 12 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (365 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_365 :
    recurrence2Scalar3Shift.coeff 365 =
      -((19222 * 10 ^ 70 +
        4723116937040079734726739575414717689070899626466290896544913650486945) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 136 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 11 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (366 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_366 :
    recurrence2Scalar3Shift.coeff 366 =
      ((1 * 10 ^ 70 +
        5171791846473585029461913609637339901287956700507924355201482925353965) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 137 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 10 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (367 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_367 :
    recurrence2Scalar3Shift.coeff 367 =
      (-326748467231985099277039007699553112269302401102927411775581648598 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 138 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 9 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (368 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_368 :
    recurrence2Scalar3Shift.coeff 368 =
      (1866921889427777477585165710501847736200764144627540842918583 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 139 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 8 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (369 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_369 :
    recurrence2Scalar3Shift.coeff 369 =
      (1992955521863482669546903058786574235939405405654698452 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 140 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 7 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (370 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_370 :
    recurrence2Scalar3Shift.coeff 370 =
      (-22194740933985694963963876171341280510094357767775 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 141 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 6 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (371 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_371 :
    recurrence2Scalar3Shift.coeff 371 =
      (18495588673549012232517070907111886696608400 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 142 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 5 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (372 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_372 :
    recurrence2Scalar3Shift.coeff 372 =
      (-2428415422479462826016467479132468682 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 143 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 4 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (373 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_373 :
    recurrence2Scalar3Shift.coeff 373 =
      (14109381873722360030037538062 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 144 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 3 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (374 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_374 :
    recurrence2Scalar3Shift.coeff 374 =
      (14623435900183798807 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 145 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 2 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Shift_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (375 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_375 :
    recurrence2Scalar3Shift.coeff 375 =
      (-22256050974 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 146 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 1 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
