/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Left coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2LeadingSquare_coeff_0
  recurrence2LeadingSquare_coeff_1
  recurrence2LeadingSquare_coeff_2
  recurrence2LeadingSquare_coeff_3
  recurrence2LeadingSquare_coeff_4
  recurrence2LeadingSquare_coeff_5
  recurrence2LeadingSquare_coeff_6
  recurrence2LeadingSquare_coeff_7
  recurrence2LeadingSquare_coeff_8
  recurrence2LeadingSquare_coeff_9
  recurrence2LeadingSquare_coeff_10
  recurrence2LeadingSquare_coeff_11
  recurrence2LeadingSquare_coeff_12
  recurrence2LeadingSquare_coeff_13
  recurrence2LeadingSquare_coeff_14
  recurrence2LeadingSquare_coeff_15
  recurrence2LeadingSquare_coeff_16
  recurrence2LeadingSquare_coeff_17
  recurrence2LeadingSquare_coeff_18
  recurrence2LeadingSquare_coeff_19
  recurrence2LeadingSquare_coeff_20
  recurrence2LeadingSquare_coeff_21
  recurrence2LeadingSquare_coeff_22
  recurrence2LeadingSquare_coeff_23
  recurrence2LeadingSquare_coeff_24
  recurrence2LeadingSquare_coeff_25
  recurrence2LeadingSquare_coeff_26
  recurrence2LeadingSquare_coeff_27
  recurrence2LeadingSquare_coeff_28
  recurrence2LeadingSquare_coeff_29
  recurrence2LeadingSquare_coeff_30
  recurrence2LeadingSquare_coeff_31
  recurrence2LeadingSquare_coeff_32
  recurrence2LeadingSquare_coeff_33
  recurrence2LeadingSquare_coeff_34
  recurrence2LeadingSquare_coeff_35
  recurrence2LeadingSquare_coeff_36
  recurrence2LeadingSquare_coeff_37
  recurrence2LeadingSquare_coeff_38
  recurrence2LeadingSquare_coeff_39
  recurrence2LeadingSquare_coeff_40
  recurrence2LeadingSquare_coeff_41
  recurrence2LeadingSquare_coeff_42
  recurrence2LeadingSquare_coeff_43
  recurrence2LeadingSquare_coeff_44
  recurrence2LeadingSquare_coeff_45
  recurrence2LeadingSquare_coeff_46
  recurrence2LeadingSquare_coeff_47
  recurrence2LeadingSquare_coeff_48
  recurrence2LeadingSquare_coeff_49
  recurrence2LeadingSquare_coeff_50
  recurrence2LeadingSquare_coeff_51
  recurrence2LeadingSquare_coeff_52
  recurrence2LeadingSquare_coeff_53
  recurrence2LeadingSquare_coeff_54
  recurrence2LeadingSquare_coeff_55
  recurrence2LeadingSquare_coeff_56
  recurrence2LeadingSquare_coeff_57
  recurrence2LeadingSquare_coeff_58
  recurrence2LeadingSquare_coeff_59
  recurrence2LeadingSquare_coeff_60
  recurrence2LeadingSquare_coeff_61
  recurrence2LeadingSquare_coeff_62
  recurrence2LeadingSquare_coeff_63
  recurrence2LeadingSquare_coeff_64
  recurrence2LeadingSquare_coeff_65
  recurrence2LeadingSquare_coeff_66
  recurrence2LeadingSquare_coeff_67
  recurrence2LeadingSquare_coeff_68
  recurrence2LeadingSquare_coeff_69
  recurrence2LeadingSquare_coeff_70
  recurrence2LeadingSquare_coeff_71
  recurrence2LeadingSquare_coeff_72
  recurrence2LeadingSquare_coeff_73
  recurrence2LeadingSquare_coeff_74
  recurrence2LeadingSquare_coeff_75
  recurrence2LeadingSquare_coeff_76
  recurrence2LeadingSquare_coeff_77
  recurrence2LeadingSquare_coeff_78
  recurrence2LeadingSquare_coeff_79
  recurrence2LeadingSquare_coeff_80
  recurrence2LeadingSquare_coeff_81
  recurrence2LeadingSquare_coeff_82
  recurrence2LeadingSquare_coeff_83
  recurrence2LeadingSquare_coeff_84
  recurrence2LeadingSquare_coeff_85
  recurrence2LeadingSquare_coeff_86
  recurrence2LeadingSquare_coeff_87
  recurrence2LeadingSquare_coeff_88
  recurrence2LeadingSquare_coeff_89
  recurrence2LeadingSquare_coeff_90
  recurrence2LeadingSquare_coeff_91
  recurrence2LeadingSquare_coeff_92
  recurrence2LeadingSquare_coeff_93
  recurrence2LeadingSquare_coeff_94
  recurrence2LeadingSquare_coeff_95
  recurrence2LeadingSquare_coeff_96
  recurrence2LeadingSquare_coeff_97
  recurrence2LeadingSquare_coeff_98
  recurrence2LeadingSquare_coeff_99
  recurrence2LeadingSquare_coeff_100
  recurrence2LeadingSquare_coeff_101
  recurrence2LeadingSquare_coeff_102
  recurrence2LeadingSquare_coeff_103
  recurrence2LeadingSquare_coeff_104
  recurrence2LeadingSquare_coeff_105
  recurrence2LeadingSquare_coeff_106
  recurrence2LeadingSquare_coeff_107
  recurrence2LeadingSquare_coeff_108
  recurrence2LeadingSquare_coeff_109
  recurrence2LeadingSquare_coeff_110
  recurrence2LeadingSquare_coeff_111
  recurrence2LeadingSquare_coeff_112
  recurrence2LeadingSquare_coeff_113
  recurrence2LeadingSquare_coeff_114
  recurrence2LeadingSquare_coeff_115
  recurrence2LeadingSquare_coeff_116
  recurrence2LeadingSquare_coeff_117
  recurrence2LeadingSquare_coeff_118
  recurrence2LeadingSquare_coeff_119
  recurrence2LeadingSquare_coeff_120
  recurrence2LeadingSquare_coeff_121
  recurrence2LeadingSquare_coeff_122
  recurrence2LeadingSquare_coeff_123
  recurrence2LeadingSquare_coeff_124
  recurrence2LeadingSquare_coeff_125
  recurrence2LeadingSquare_coeff_126
  recurrence2LeadingSquare_coeff_127
  recurrence2LeadingSquare_coeff_128
  recurrence2LeadingSquare_coeff_129
  recurrence2LeadingSquare_coeff_130
  recurrence2LeadingSquare_coeff_131
  recurrence2LeadingSquare_coeff_132
  recurrence2LeadingSquare_coeff_133
  recurrence2LeadingSquare_coeff_134
  recurrence2LeadingSquare_coeff_135
  recurrence2LeadingSquare_coeff_136
  recurrence2LeadingSquare_coeff_137
  recurrence2LeadingSquare_coeff_138
  recurrence2LeadingSquare_coeff_139
  recurrence2LeadingSquare_coeff_140
  recurrence2LeadingSquare_coeff_141
  recurrence2LeadingSquare_coeff_142
  recurrence2LeadingSquare_coeff_143
  recurrence2LeadingSquare_coeff_144
  recurrence2LeadingSquare_coeff_145
  recurrence2LeadingSquare_coeff_146
  recurrence2LeadingSquare_coeff_147
  recurrence2LeadingSquare_coeff_148
  recurrence2LeadingSquare_coeff_149
  recurrence2LeadingSquare_coeff_150
  recurrence2LeadingSquare_coeff_151
  recurrence2LeadingSquare_coeff_152
  recurrence2LeadingSquare_coeff_153
  recurrence2LeadingSquare_coeff_154
  recurrence2LeadingSquare_coeff_155
  recurrence2LeadingSquare_coeff_156
  recurrence2LeadingSquare_coeff_157
  recurrence2LeadingSquare_coeff_158
  recurrence2LeadingSquare_coeff_159
  recurrence2LeadingSquare_coeff_160
  recurrence2LeadingSquare_coeff_161
  recurrence2LeadingSquare_coeff_162
  recurrence2LeadingSquare_coeff_163
  recurrence2LeadingSquare_coeff_164
  recurrence2LeadingSquare_coeff_165
  recurrence2LeadingSquare_coeff_166
  recurrence2LeadingSquare_coeff_167
  recurrence2LeadingSquare_coeff_168
  recurrence2LeadingSquare_coeff_169
  recurrence2LeadingSquare_coeff_170
  recurrence2LeadingSquare_coeff_171
  recurrence2LeadingSquare_coeff_172
  recurrence2LeadingSquare_coeff_173
  recurrence2LeadingSquare_coeff_174
  recurrence2LeadingSquare_coeff_175
  recurrence2LeadingSquare_coeff_176
  recurrence2LeadingSquare_coeff_177
  recurrence2LeadingSquare_coeff_178
  recurrence2LeadingSquare_coeff_179
  recurrence2LeadingSquare_coeff_180
  recurrence2LeadingSquare_coeff_181
  recurrence2LeadingSquare_coeff_182
  recurrence2LeadingSquare_coeff_183
  recurrence2LeadingSquare_coeff_184
  recurrence2LeadingSquare_coeff_185
  recurrence2LeadingSquare_coeff_186
  recurrence2LeadingSquare_coeff_187
  recurrence2LeadingSquare_coeff_188
  recurrence2LeadingSquare_coeff_189
  recurrence2LeadingSquare_coeff_190
  recurrence2LeadingSquare_coeff_191
  recurrence2LeadingSquare_coeff_192
  recurrence2LeadingSquare_coeff_193
  recurrence2LeadingSquare_coeff_194
  recurrence2LeadingSquare_coeff_195
  recurrence2LeadingSquare_coeff_196
  recurrence2LeadingSquare_coeff_197
  recurrence2LeadingSquare_coeff_198
  recurrence2LeadingSquare_coeff_199
  recurrence2LeadingSquare_coeff_200
  recurrence2LeadingSquare_coeff_201
  recurrence2LeadingSquare_coeff_202
  recurrence2LeadingSquare_coeff_203
  recurrence2LeadingSquare_coeff_204
  recurrence2LeadingSquare_coeff_205
  recurrence2LeadingSquare_coeff_206
  recurrence2LeadingSquare_coeff_207
  recurrence2LeadingSquare_coeff_208
  recurrence2LeadingSquare_coeff_209
  recurrence2LeadingSquare_coeff_210
  recurrence2LeadingSquare_coeff_211
  recurrence2LeadingSquare_coeff_212
  recurrence2LeadingSquare_coeff_213
  recurrence2LeadingSquare_coeff_214
  recurrence2LeadingSquare_coeff_215
  recurrence2LeadingSquare_coeff_216
  recurrence2LeadingSquare_coeff_217
  recurrence2LeadingSquare_coeff_218
  recurrence2LeadingSquare_coeff_219
  recurrence2LeadingSquare_coeff_220
  recurrence2LeadingSquare_coeff_221
  recurrence2LeadingSquare_coeff_222
  recurrence2LeadingSquare_coeff_223
  recurrence2LeadingSquare_coeff_224
  recurrence2LeadingSquare_coeff_225
  recurrence2LeadingSquare_coeff_226
  recurrence2LeadingSquare_coeff_227
  recurrence2LeadingSquare_coeff_228
  recurrence2LeadingSquare_coeff_229
  recurrence2LeadingSquare_coeff_230
  recurrence2LeadingSquare_coeff_231
  recurrence2LeadingSquare_coeff_232
  recurrence2LeadingSquare_coeff_233
  recurrence2LeadingSquare_coeff_234
  recurrence2LeadingSquare_coeff_235
  recurrence2LeadingSquare_coeff_236
  recurrence2LeadingSquare_coeff_237
  recurrence2LeadingSquare_coeff_238
  recurrence2LeadingSquare_coeff_239
  recurrence2LeadingSquare_coeff_240
  recurrence2LeadingSquare_coeff_241
  recurrence2LeadingSquare_coeff_242
  recurrence2LeadingSquare_coeff_243
  recurrence2LeadingSquare_coeff_244
  recurrence2LeadingSquare_coeff_245
  recurrence2LeadingSquare_coeff_246
  recurrence2LeadingSquare_coeff_247
  recurrence2LeadingSquare_coeff_248
  recurrence2LeadingSquare_coeff_249
  recurrence2LeadingSquare_coeff_250
  recurrence2LeadingSquare_coeff_251
  recurrence2LeadingSquare_coeff_252
  recurrence2LeadingSquare_coeff_253
  recurrence2LeadingSquare_coeff_254
  recurrence2LeadingSquare_coeff_255
  recurrence2LeadingSquare_coeff_256
  recurrence2LeadingSquare_coeff_257
  recurrence2LeadingSquare_coeff_258
  recurrence2LeadingSquare_coeff_259
  recurrence2LeadingSquare_coeff_260
  recurrence2LeadingSquare_coeff_261
  recurrence2LeadingSquare_coeff_262
  recurrence2LeadingSquare_coeff_263
  recurrence2LeadingSquare_coeff_264
  recurrence2LeadingSquare_coeff_265
  recurrence2LeadingSquare_coeff_266
  recurrence2LeadingSquare_coeff_267
  recurrence2LeadingSquare_coeff_268
  recurrence2A4_coeff_0
  recurrence2A4_coeff_1
  recurrence2A4_coeff_2
  recurrence2A4_coeff_3
  recurrence2A4_coeff_4
  recurrence2A4_coeff_5
  recurrence2A4_coeff_6
  recurrence2A4_coeff_7
  recurrence2A4_coeff_8
  recurrence2A4_coeff_9
  recurrence2A4_coeff_10
  recurrence2A4_coeff_11
  recurrence2A4_coeff_12
  recurrence2A4_coeff_13
  recurrence2A4_coeff_14
  recurrence2A4_coeff_15
  recurrence2A4_coeff_16
  recurrence2A4_coeff_17
  recurrence2A4_coeff_18
  recurrence2A4_coeff_19
  recurrence2A4_coeff_20
  recurrence2A4_coeff_21
  recurrence2A4_coeff_22
  recurrence2A4_coeff_23
  recurrence2A4_coeff_24
  recurrence2A4_coeff_25
  recurrence2A4_coeff_26
  recurrence2A4_coeff_27
  recurrence2A4_coeff_28
  recurrence2A4_coeff_29
  recurrence2A4_coeff_30
  recurrence2A4_coeff_31
  recurrence2A4_coeff_32
  recurrence2A4_coeff_33
  recurrence2A4_coeff_34
  recurrence2A4_coeff_35
  recurrence2A4_coeff_36
  recurrence2A4_coeff_37
  recurrence2A4_coeff_38
  recurrence2A4_coeff_39
  recurrence2A4_coeff_40
  recurrence2A4_coeff_41
  recurrence2A4_coeff_42
  recurrence2A4_coeff_43
  recurrence2A4_coeff_44
  recurrence2A4_coeff_45
  recurrence2A4_coeff_46
  recurrence2A4_coeff_47
  recurrence2A4_coeff_48
  recurrence2A4_coeff_49
  recurrence2A4_coeff_50
  recurrence2A4_coeff_51
  recurrence2A4_coeff_52
  recurrence2A4_coeff_53
  recurrence2A4_coeff_54
  recurrence2A4_coeff_55
  recurrence2A4_coeff_56
  recurrence2A4_coeff_57
  recurrence2A4_coeff_58
  recurrence2A4_coeff_59
  recurrence2A4_coeff_60
  recurrence2A4_coeff_61
  recurrence2A4_coeff_62
  recurrence2A4_coeff_63
  recurrence2A4_coeff_64
  recurrence2A4_coeff_65
  recurrence2A4_coeff_66
  recurrence2A4_coeff_67
  recurrence2A4_coeff_68
  recurrence2A4_coeff_69
  recurrence2A4_coeff_70
  recurrence2A4_coeff_71
  recurrence2A4_coeff_72
  recurrence2A4_coeff_73
  recurrence2A4_coeff_74
  recurrence2A4_coeff_75
  recurrence2A4_coeff_76
  recurrence2A4_coeff_77
  recurrence2A4_coeff_78
  recurrence2A4_coeff_79
  recurrence2A4_coeff_80
  recurrence2A4_coeff_81
  recurrence2A4_coeff_82
  recurrence2A4_coeff_83
  recurrence2A4_coeff_84
  recurrence2A4_coeff_85
  recurrence2A4_coeff_86
  recurrence2A4_coeff_87
  recurrence2A4_coeff_88
  recurrence2A4_coeff_89
  recurrence2A4_coeff_90
  recurrence2A4_coeff_91
  recurrence2A4_coeff_92
  recurrence2A4_coeff_93
  recurrence2A4_coeff_94
  recurrence2A4_coeff_95
  recurrence2A4_coeff_96
  recurrence2A4_coeff_97
  recurrence2A4_coeff_98
  recurrence2A4_coeff_99
  recurrence2A4_coeff_100
  recurrence2A4_coeff_101
  recurrence2A4_coeff_102

private theorem recurrence2Scalar4Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (300 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_300 :
    recurrence2Scalar4Left.coeff 300 =
      (((160359386251253468884441420610234248122257096419 * 10 ^ 70 +
        7325376981043509728498729565686362928858646053342223978847134287061060) * 10 ^ 70 +
        7190628805428195371251394900828107870740144104014727126727550416756501) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 198 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 7 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (301 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_301 :
    recurrence2Scalar4Left.coeff 301 =
      -(((50116524048406953325530039561417338507847949432 * 10 ^ 70 +
        4953944529592946030648021562746295771887473331301413525458664561109152) * 10 ^ 70 +
        0036200932603394558043243980956704378010486146886835993933587827822674) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 199 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 6 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (302 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_302 :
    recurrence2Scalar4Left.coeff 302 =
      (((11056320440557132128784313449103744195230150003 * 10 ^ 70 +
        9925511554683092033670660017667543043433370928173083530766354663186324) * 10 ^ 70 +
        0956869841323208142207515072965485943325977372081113231512773964525878) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 200 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 5 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (303 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_303 :
    recurrence2Scalar4Left.coeff 303 =
      -(((1986429326644189051790649151302542565372737318 * 10 ^ 70 +
        3037768203659523103771165972651521526752322564459564861027206673254388) * 10 ^ 70 +
        4855072268856019502286765541586645091272134475894196788312724760627243) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 201 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 4 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (304 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_304 :
    recurrence2Scalar4Left.coeff 304 =
      (((300384201942940909474394246140022834990362000 * 10 ^ 70 +
        8977369912012073263594589446716693820146319190378250918399604304393074) * 10 ^ 70 +
        8732230563317663258886882783847542852815433387483938196328616690570167) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 202 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 3 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (305 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_305 :
    recurrence2Scalar4Left.coeff 305 =
      -(((37887118265875791967251711788289700533038508 * 10 ^ 70 +
        6533826581224979407586067273942865971403147426221721140546192145898320) * 10 ^ 70 +
        0726929374892832272958096252782255862288935301309759210949573467614524) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 203 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 2 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (306 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_306 :
    recurrence2Scalar4Left.coeff 306 =
      (((3749306866041689569241177994271119983453582 * 10 ^ 70 +
        1726607596701223584366352526961290154063627982804913329330829895930777) * 10 ^ 70 +
        5673794523693410863694200007439532284767042571707048312231353265341421) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 204 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 1 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (307 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_307 :
    recurrence2Scalar4Left.coeff 307 =
      -(((223804707954681907187948623697120500127640 * 10 ^ 70 +
        3489708054539992649576038521348026260730161658329709257975617137020485) * 10 ^ 70 +
        3503052444921474688182828690043099532595558539177900374987837419224571) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 205 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (308 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_308 :
    recurrence2Scalar4Left.coeff 308 =
      -(((11097934754497342824802481279977535681678 * 10 ^ 70 +
        1410351501819987238569606251934183146004617964461317500382410181934239) * 10 ^ 70 +
        1951128550541142041817016422924155861337889762285901099636846094341656) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 206 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 31 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (309 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_309 :
    recurrence2Scalar4Left.coeff 309 =
      (((5984492140492639448593699727929150105033 * 10 ^ 70 +
        5130841109654528807654591789124780724849141552919234700157224079705942) * 10 ^ 70 +
        2513516524804124904370325506680968568710725361955115310152042954766542) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 207 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 30 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (310 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_310 :
    recurrence2Scalar4Left.coeff 310 =
      -(((1120586807806938251780508664817891378882 * 10 ^ 70 +
        1682136914730401424012170732019441634345386851070166324232014416562564) * 10 ^ 70 +
        4290972261963081362299582118282339219607241049556373297610350343455219) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 208 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 29 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (311 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_311 :
    recurrence2Scalar4Left.coeff 311 =
      (((149746556243386498316250828650327150657 * 10 ^ 70 +
        6459160104712444251123146460184465260846962113444819859349682361085653) * 10 ^ 70 +
        5878750394391540470621381949286703394712628875164291194839970046349835) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 209 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 28 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (312 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_312 :
    recurrence2Scalar4Left.coeff 312 =
      -(((15612562383060552368678934137722856702 * 10 ^ 70 +
        6086217019628516780378856910622971698196441000613797222629573380771443) * 10 ^ 70 +
        3196998942946708733217692005056347804435364838167017489148648820577973) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 210 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 27 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (313 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_313 :
    recurrence2Scalar4Left.coeff 313 =
      (((1247683627950169980838672816690100035 * 10 ^ 70 +
        3462268187960740609417412416777446652671438874595187445030562618794054) * 10 ^ 70 +
        2406722018445264507622743603163910958211455534143949865888532329035407) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 211 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 26 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (314 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_314 :
    recurrence2Scalar4Left.coeff 314 =
      -(((64848876924386162888483252354049686 * 10 ^ 70 +
        4477812282382117056631864391210195359858297931947417419329164361397141) * 10 ^ 70 +
        4623049815244298129979244743779027600450950891971922418155829115079004) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 212 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 25 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (315 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_315 :
    recurrence2Scalar4Left.coeff 315 =
      -(((192275594197665478526966137825972 * 10 ^ 70 +
        4725905380655428751910169796244030171230621316877324501024806114155543) * 10 ^ 70 +
        7269958966267819695326291865746065735023690394409898805191222435483701) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 213 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 24 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (316 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_316 :
    recurrence2Scalar4Left.coeff 316 =
      (((519427982401639004912413977515937 * 10 ^ 70 +
        3927167308220069452503075177658340771596592939435562912034771564534809) * 10 ^ 70 +
        6695981572821137175885526340778644086100434614138785184129883685664146) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 214 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 23 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (317 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_317 :
    recurrence2Scalar4Left.coeff 317 =
      -(((71597981297806606557457535349424 * 10 ^ 70 +
        5322506157271150689236560853673265905326580681910206938421808339961488) * 10 ^ 70 +
        4174290702141116190510541197691636407355534717927961735056747957570606) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 215 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 22 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (318 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_318 :
    recurrence2Scalar4Left.coeff 318 =
      (((6274652056296817880723290048890 * 10 ^ 70 +
        1135187625387476834036650546583680980358770991139493965099327174000165) * 10 ^ 70 +
        8007241533952954160000565889484559489928652077838249476594296397105989) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 216 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 21 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (319 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_319 :
    recurrence2Scalar4Left.coeff 319 =
      -(((387361874790552835312278056070 * 10 ^ 70 +
        5416048999461332536882103005943984464538949197880634999348740639636280) * 10 ^ 70 +
        4419121030405693727171050724468776358137751615703228840034441402549164) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 217 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 20 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (320 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_320 :
    recurrence2Scalar4Left.coeff 320 =
      (((14772646335933128843435621081 * 10 ^ 70 +
        1760238464388772921982209617832912657333947777130669110083749757120636) * 10 ^ 70 +
        4943039631902350746891976757242131375362755749272034679653794514511948) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 218 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 19 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (321 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_321 :
    recurrence2Scalar4Left.coeff 321 =
      (((17111688351377641039184110 * 10 ^ 70 +
        7372765275977075994307622378964915263113902086981144407922540991064826) * 10 ^ 70 +
        8713748405918930169085544232615538562922448986055722272133635172324473) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 219 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 18 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (322 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_322 :
    recurrence2Scalar4Left.coeff 322 =
      -(((52861037871744305885706026 * 10 ^ 70 +
        8916308285172712356805305797279665716992036965953767687963125079376485) * 10 ^ 70 +
        2657456883457182773951877435848065770547492818922198334353532963072979) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 220 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 17 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (323 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_323 :
    recurrence2Scalar4Left.coeff 323 =
      (((4558195127172449831761844 * 10 ^ 70 +
        8554182967197581377118672756613464013851159465375155202802409049516694) * 10 ^ 70 +
        1550021921401083351619695456292665657300765932054871904374385368870952) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 221 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 16 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (324 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_324 :
    recurrence2Scalar4Left.coeff 324 =
      -(((226822497008526634223944 * 10 ^ 70 +
        4466509501600296576592197467063174857474978178130185756925086393100550) * 10 ^ 70 +
        9204173221754642605166509600156016239217812706150054436349823219961556) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 222 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 15 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (325 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_325 :
    recurrence2Scalar4Left.coeff 325 =
      (((6430169609810213317289 * 10 ^ 70 +
        1547284969871456373255252159396441466455360998590773958569343126684266) * 10 ^ 70 +
        9558577491701921766640224607436146500930688459492591551605369615606970) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 223 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 14 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (326 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_326 :
    recurrence2Scalar4Left.coeff 326 =
      -(((3392109436877748553 * 10 ^ 70 +
        0021486191473575399750325388207113094785060380135619555876773515429026) * 10 ^ 70 +
        1203789316121550926455755286918196995007309497362873591966843321848941) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 224 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 13 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (327 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_327 :
    recurrence2Scalar4Left.coeff 327 =
      -(((9489174440506190127 * 10 ^ 70 +
        2822190197992529577789713653099339356852512117212088837449386696559582) * 10 ^ 70 +
        0272898301018679564507653960748798917728858994642995288627695436594244) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 225 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 12 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (328 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_328 :
    recurrence2Scalar4Left.coeff 328 =
      (((486629160155821677 * 10 ^ 70 +
        5565227717032201278967805041735340739804014468332113258446587235064499) * 10 ^ 70 +
        4728772221678453858173911328059258543567288124771853734015481147146540) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 226 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 11 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (329 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_329 :
    recurrence2Scalar4Left.coeff 329 =
      -(((12126137477962286 * 10 ^ 70 +
        2999023655136556585076217040508743220389607323606454627480457614175549) * 10 ^ 70 +
        1023775681804839469512634787981283347042815140726257495069540967738600) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 227 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 10 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (330 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_330 :
    recurrence2Scalar4Left.coeff 330 =
      (((74848295666186 * 10 ^ 70 +
        3587339622996565828537796390743549053704537230415554488964902285689733) * 10 ^ 70 +
        3127348962127905500167635623016040891595978052739030473566062619781345) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 228 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 9 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (331 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_331 :
    recurrence2Scalar4Left.coeff 331 =
      (((5311391525070 * 10 ^ 70 +
        2973119216784174221792094074630937691200571351610716893358581453620007) * 10 ^ 70 +
        2929482461418536990072248888143524670507477721665310411638861805271119) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 229 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 8 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (332 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_332 :
    recurrence2Scalar4Left.coeff 332 =
      -(((186865512112 * 10 ^ 70 +
        7958659746920370649075130446519704506948702048741464564932809475762994) * 10 ^ 70 +
        7132103873163727649049195536186099607325463084626502128942387239050614) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 230 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 7 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
