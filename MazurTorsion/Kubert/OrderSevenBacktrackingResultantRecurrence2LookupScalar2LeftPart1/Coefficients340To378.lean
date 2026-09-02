/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Left coefficient convolution

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
  recurrence2A2_coeff_0
  recurrence2A2_coeff_1
  recurrence2A2_coeff_2
  recurrence2A2_coeff_3
  recurrence2A2_coeff_4
  recurrence2A2_coeff_5
  recurrence2A2_coeff_6
  recurrence2A2_coeff_7
  recurrence2A2_coeff_8
  recurrence2A2_coeff_9
  recurrence2A2_coeff_10
  recurrence2A2_coeff_11
  recurrence2A2_coeff_12
  recurrence2A2_coeff_13
  recurrence2A2_coeff_14
  recurrence2A2_coeff_15
  recurrence2A2_coeff_16
  recurrence2A2_coeff_17
  recurrence2A2_coeff_18
  recurrence2A2_coeff_19
  recurrence2A2_coeff_20
  recurrence2A2_coeff_21
  recurrence2A2_coeff_22
  recurrence2A2_coeff_23
  recurrence2A2_coeff_24
  recurrence2A2_coeff_25
  recurrence2A2_coeff_26
  recurrence2A2_coeff_27
  recurrence2A2_coeff_28
  recurrence2A2_coeff_29
  recurrence2A2_coeff_30
  recurrence2A2_coeff_31
  recurrence2A2_coeff_32
  recurrence2A2_coeff_33
  recurrence2A2_coeff_34
  recurrence2A2_coeff_35
  recurrence2A2_coeff_36
  recurrence2A2_coeff_37
  recurrence2A2_coeff_38
  recurrence2A2_coeff_39
  recurrence2A2_coeff_40
  recurrence2A2_coeff_41
  recurrence2A2_coeff_42
  recurrence2A2_coeff_43
  recurrence2A2_coeff_44
  recurrence2A2_coeff_45
  recurrence2A2_coeff_46
  recurrence2A2_coeff_47
  recurrence2A2_coeff_48
  recurrence2A2_coeff_49
  recurrence2A2_coeff_50
  recurrence2A2_coeff_51
  recurrence2A2_coeff_52
  recurrence2A2_coeff_53
  recurrence2A2_coeff_54
  recurrence2A2_coeff_55
  recurrence2A2_coeff_56
  recurrence2A2_coeff_57
  recurrence2A2_coeff_58
  recurrence2A2_coeff_59
  recurrence2A2_coeff_60
  recurrence2A2_coeff_61
  recurrence2A2_coeff_62
  recurrence2A2_coeff_63
  recurrence2A2_coeff_64
  recurrence2A2_coeff_65
  recurrence2A2_coeff_66
  recurrence2A2_coeff_67
  recurrence2A2_coeff_68
  recurrence2A2_coeff_69
  recurrence2A2_coeff_70
  recurrence2A2_coeff_71
  recurrence2A2_coeff_72
  recurrence2A2_coeff_73
  recurrence2A2_coeff_74
  recurrence2A2_coeff_75
  recurrence2A2_coeff_76
  recurrence2A2_coeff_77
  recurrence2A2_coeff_78
  recurrence2A2_coeff_79
  recurrence2A2_coeff_80
  recurrence2A2_coeff_81
  recurrence2A2_coeff_82
  recurrence2A2_coeff_83
  recurrence2A2_coeff_84
  recurrence2A2_coeff_85
  recurrence2A2_coeff_86
  recurrence2A2_coeff_87
  recurrence2A2_coeff_88
  recurrence2A2_coeff_89
  recurrence2A2_coeff_90
  recurrence2A2_coeff_91
  recurrence2A2_coeff_92
  recurrence2A2_coeff_93
  recurrence2A2_coeff_94
  recurrence2A2_coeff_95
  recurrence2A2_coeff_96
  recurrence2A2_coeff_97
  recurrence2A2_coeff_98
  recurrence2A2_coeff_99
  recurrence2A2_coeff_100
  recurrence2A2_coeff_101
  recurrence2A2_coeff_102
  recurrence2A2_coeff_103
  recurrence2A2_coeff_104
  recurrence2A2_coeff_105
  recurrence2A2_coeff_106
  recurrence2A2_coeff_107
  recurrence2A2_coeff_108
  recurrence2A2_coeff_109
  recurrence2A2_coeff_110

private theorem recurrence2Scalar2Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (340 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_340 :
    recurrence2Scalar2Left.coeff 340 =
      -(((40708407017 * 10 ^ 70 +
        8504022484933540598833242249133096394891875824398006365427428632934663) * 10 ^ 70 +
        2043608291140668427114048956423025649533008655223002133016964080573854) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 230 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 7 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (341 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_341 :
    recurrence2Scalar2Left.coeff 341 =
      (((634631686 * 10 ^ 70 +
        3742985392917109849977339316151991937632756486920873968074292639691605) * 10 ^ 70 +
        5263716612608886088961367119087799424711570427859971232058823252702357) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 231 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 6 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (342 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_342 :
    recurrence2Scalar2Left.coeff 342 =
      -(((141585 * 10 ^ 70 +
        5781915359238123969400060388662028737397891803528403729045367528183708) * 10 ^ 70 +
        9447118960331124915370297144611248012986982184958116820432038310939834) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 232 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 5 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (343 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_343 :
    recurrence2Scalar2Left.coeff 343 =
      -(((137958 * 10 ^ 70 +
        6067080147428829535913947132489682643028212328858975140820298332914754) * 10 ^ 70 +
        1422661978780556683980295405168599734725089766664923133291917057384832) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 233 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 4 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (344 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_344 :
    recurrence2Scalar2Left.coeff 344 =
      (((1666 * 10 ^ 70 +
        6708684550033839668658984277347252104802747870111899347665281492102261) * 10 ^ 70 +
        8051853403921508876028752526491148034058602346745360116226737192044339) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 234 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 3 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (345 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_345 :
    recurrence2Scalar2Left.coeff 345 =
      (((2 * 10 ^ 70 +
        3077150461792369414461759803145344781523149488193016747887319212309355) * 10 ^ 70 +
        5488028719859956711567979293530239170599576121172397015609585197556313) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 235 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 2 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (346 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_346 :
    recurrence2Scalar2Left.coeff 346 =
      -((1804471947942635003028027279223331276003470183176823465239562817855022 * 10 ^ 70 +
        8218362127691463035236126946200286600228152727489593920375776172635529) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 236 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 1 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (347 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_347 :
    recurrence2Scalar2Left.coeff 347 =
      ((7795996385656912117607016265998944504198808066702154529842141931609 * 10 ^ 70 +
        3679465891171055282453238312107624153294132633931610937941244504857688) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 237 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (348 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_348 :
    recurrence2Scalar2Left.coeff 348 =
      ((77370453674922051339538767665300552521681502470316296352204762856 * 10 ^ 70 +
        6433015689437960898403963130389135913706118560036823881932888980107999) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 238 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 31 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (349 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_349 :
    recurrence2Scalar2Left.coeff 349 =
      -((610025508901501215157421317594029468876334287722601850013513524 * 10 ^ 70 +
        1328822544467791436028545018175221741155440205511190974030333254768612) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 239 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 30 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (350 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_350 :
    recurrence2Scalar2Left.coeff 350 =
      -((1381797314573962088702339675965693583262010261117877094334892 * 10 ^ 70 +
        9969038555257337079722954490779913165833718679387569761644331581310844) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 240 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 29 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (351 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_351 :
    recurrence2Scalar2Left.coeff 351 =
      ((20508955284546651535880119579542971692849146436304705756823 * 10 ^ 70 +
        7113872019016680717576408952860218371870123447720877524719206169741818) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 241 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 28 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (352 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_352 :
    recurrence2Scalar2Left.coeff 352 =
      -((2542568150077443108637755644014902200395149114143348778 * 10 ^ 70 +
        5514232751889585870894323052897113967278107840068294402028269686239849) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 242 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 27 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (353 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_353 :
    recurrence2Scalar2Left.coeff 353 =
      -((364863057946255163615247076886654957755118548827579359 * 10 ^ 70 +
        1178631619699265435713397124160389837177166053433042165295334905115536) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 243 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 26 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (354 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_354 :
    recurrence2Scalar2Left.coeff 354 =
      ((532200493993842524544307930536907574353935483020983 * 10 ^ 70 +
        8576632966863146084937107244670182106326551930643757034743278924189547) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 244 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 25 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (355 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_355 :
    recurrence2Scalar2Left.coeff 355 =
      ((3365148061082629138355466629996445736086283273840 * 10 ^ 70 +
        3912388244156226477667596266133142492477200675891641423047100504607328) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 245 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 24 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (356 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_356 :
    recurrence2Scalar2Left.coeff 356 =
      -((8958673106345730467956178475423282083134446884 * 10 ^ 70 +
        2395612599131988392970163620874446062573250835664554325935554383436863) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 246 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 23 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (357 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_357 :
    recurrence2Scalar2Left.coeff 357 =
      -((11526276649966096593593846001241934408592380 * 10 ^ 70 +
        5457445805886603053311948087836970204988935937548064543980262654224803) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 247 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 22 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (358 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_358 :
    recurrence2Scalar2Left.coeff 358 =
      ((62230281519292080353328103661998284136149 * 10 ^ 70 +
        4992570157082701856866919567571203326389998140440556305057296342766707) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 248 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 21 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (359 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_359 :
    recurrence2Scalar2Left.coeff 359 =
      -((34005294992908469187483516233116000627 * 10 ^ 70 +
        9113883548582348149409454813520524197440068427726273191539809148720134) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 249 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 20 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (360 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_360 :
    recurrence2Scalar2Left.coeff 360 =
      -((143476662966419478070951742551888422 * 10 ^ 70 +
        2975823137217593690026078456837171351277536306294630672209454120228400) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 250 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 19 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (361 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_361 :
    recurrence2Scalar2Left.coeff 361 =
      ((258266752598609706894148994719421 * 10 ^ 70 +
        2355742230385039858076612216115498340760039103349558806877034038751004) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 251 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 18 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (362 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_362 :
    recurrence2Scalar2Left.coeff 362 =
      -((113508781085075293009636672752 * 10 ^ 70 +
        7964953088162664516452966131177920065816315508520004733765730301495458) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 252 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 17 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (363 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_363 :
    recurrence2Scalar2Left.coeff 363 =
      -((88517437888567200231829520 * 10 ^ 70 +
        7425513021196020965811622493663505273826014572662116905583294464840405) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 253 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 16 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (364 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_364 :
    recurrence2Scalar2Left.coeff 364 =
      ((114153677450027860522058 * 10 ^ 70 +
        4078681459268105657201641388912318448434215460345399605299010293288158) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 254 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 15 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (365 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_365 :
    recurrence2Scalar2Left.coeff 365 =
      -((44227618253274786699 * 10 ^ 70 +
        5062413085514763492116059357486171410706000749220210774888321138022335) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 255 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 14 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (366 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_366 :
    recurrence2Scalar2Left.coeff 366 =
      ((5563236681362631 * 10 ^ 70 +
        0542266726839416510313928919648634932674885773980843614507261826583244) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 256 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 13 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (367 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_367 :
    recurrence2Scalar2Left.coeff 367 =
      ((477844709148 * 10 ^ 70 +
        1805014600880623918742962448513093763835015599248972871974634773596547) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 257 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 12 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (368 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_368 :
    recurrence2Scalar2Left.coeff 368 =
      -((168675303 * 10 ^ 70 +
        2522715356130651820079075062823924418498948790867870770582464649298139) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 258 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 11 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (369 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_369 :
    recurrence2Scalar2Left.coeff 369 =
      ((12369 * 10 ^ 70 +
        3837428923292602925712172680413368041792537765336496475393651431245761) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 259 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 10 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (370 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_370 :
    recurrence2Scalar2Left.coeff 370 =
      (-3024516181811578574208994770112130437187217941495641214476521933648312 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 260 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 9 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (371 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_371 :
    recurrence2Scalar2Left.coeff 371 =
      (5593358761912299372840248274854305808116493005983842481284199347 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 261 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 8 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (372 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_372 :
    recurrence2Scalar2Left.coeff 372 =
      (349903081699219370002257669547137221463936703025739577338281 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 262 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 7 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (373 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_373 :
    recurrence2Scalar2Left.coeff 373 =
      (-2441355828325855674605786505737644789852349962246652922 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 263 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 6 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (374 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_374 :
    recurrence2Scalar2Left.coeff 374 =
      (3057882343441783644551122281669487336154913470265 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 264 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 5 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (375 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_375 :
    recurrence2Scalar2Left.coeff 375 =
      (-964966229735737416297104475168744575522188 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 265 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 4 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (376 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_376 :
    recurrence2Scalar2Left.coeff 376 =
      (-81304863666383514154862603906427012 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 266 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 3 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (377 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_377 :
    recurrence2Scalar2Left.coeff 377 =
      (1245463248866986683210561204 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 267 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 2 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (378 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_378 :
    recurrence2Scalar2Left.coeff 378 =
      (-4412933304219039693 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 268 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 1 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
