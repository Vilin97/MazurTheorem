/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Left coefficient convolution

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
  recurrence2A0_coeff_0
  recurrence2A0_coeff_1
  recurrence2A0_coeff_2
  recurrence2A0_coeff_3
  recurrence2A0_coeff_4
  recurrence2A0_coeff_5
  recurrence2A0_coeff_6
  recurrence2A0_coeff_7
  recurrence2A0_coeff_8
  recurrence2A0_coeff_9
  recurrence2A0_coeff_10
  recurrence2A0_coeff_11
  recurrence2A0_coeff_12
  recurrence2A0_coeff_13
  recurrence2A0_coeff_14
  recurrence2A0_coeff_15
  recurrence2A0_coeff_16
  recurrence2A0_coeff_17
  recurrence2A0_coeff_18
  recurrence2A0_coeff_19
  recurrence2A0_coeff_20
  recurrence2A0_coeff_21
  recurrence2A0_coeff_22
  recurrence2A0_coeff_23
  recurrence2A0_coeff_24
  recurrence2A0_coeff_25
  recurrence2A0_coeff_26
  recurrence2A0_coeff_27
  recurrence2A0_coeff_28
  recurrence2A0_coeff_29
  recurrence2A0_coeff_30
  recurrence2A0_coeff_31
  recurrence2A0_coeff_32
  recurrence2A0_coeff_33
  recurrence2A0_coeff_34
  recurrence2A0_coeff_35
  recurrence2A0_coeff_36
  recurrence2A0_coeff_37
  recurrence2A0_coeff_38
  recurrence2A0_coeff_39
  recurrence2A0_coeff_40
  recurrence2A0_coeff_41
  recurrence2A0_coeff_42
  recurrence2A0_coeff_43
  recurrence2A0_coeff_44
  recurrence2A0_coeff_45
  recurrence2A0_coeff_46
  recurrence2A0_coeff_47
  recurrence2A0_coeff_48
  recurrence2A0_coeff_49
  recurrence2A0_coeff_50
  recurrence2A0_coeff_51
  recurrence2A0_coeff_52
  recurrence2A0_coeff_53
  recurrence2A0_coeff_54
  recurrence2A0_coeff_55
  recurrence2A0_coeff_56
  recurrence2A0_coeff_57
  recurrence2A0_coeff_58
  recurrence2A0_coeff_59
  recurrence2A0_coeff_60
  recurrence2A0_coeff_61
  recurrence2A0_coeff_62
  recurrence2A0_coeff_63
  recurrence2A0_coeff_64
  recurrence2A0_coeff_65
  recurrence2A0_coeff_66
  recurrence2A0_coeff_67
  recurrence2A0_coeff_68
  recurrence2A0_coeff_69
  recurrence2A0_coeff_70
  recurrence2A0_coeff_71
  recurrence2A0_coeff_72
  recurrence2A0_coeff_73
  recurrence2A0_coeff_74
  recurrence2A0_coeff_75
  recurrence2A0_coeff_76
  recurrence2A0_coeff_77
  recurrence2A0_coeff_78
  recurrence2A0_coeff_79
  recurrence2A0_coeff_80
  recurrence2A0_coeff_81
  recurrence2A0_coeff_82
  recurrence2A0_coeff_83
  recurrence2A0_coeff_84
  recurrence2A0_coeff_85
  recurrence2A0_coeff_86
  recurrence2A0_coeff_87
  recurrence2A0_coeff_88
  recurrence2A0_coeff_89
  recurrence2A0_coeff_90
  recurrence2A0_coeff_91
  recurrence2A0_coeff_92
  recurrence2A0_coeff_93
  recurrence2A0_coeff_94
  recurrence2A0_coeff_95
  recurrence2A0_coeff_96
  recurrence2A0_coeff_97
  recurrence2A0_coeff_98
  recurrence2A0_coeff_99
  recurrence2A0_coeff_100
  recurrence2A0_coeff_101
  recurrence2A0_coeff_102
  recurrence2A0_coeff_103
  recurrence2A0_coeff_104
  recurrence2A0_coeff_105
  recurrence2A0_coeff_106
  recurrence2A0_coeff_107
  recurrence2A0_coeff_108
  recurrence2A0_coeff_109
  recurrence2A0_coeff_110
  recurrence2A0_coeff_111
  recurrence2A0_coeff_112
  recurrence2A0_coeff_113
  recurrence2A0_coeff_114
  recurrence2A0_coeff_115
  recurrence2A0_coeff_116
  recurrence2A0_coeff_117
  recurrence2A0_coeff_118

private theorem recurrence2Scalar0Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (275 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_275 :
    recurrence2Scalar0Left.coeff 275 =
      -(((630771405318048481935826172523614447396526609652313452353080547304752 * 10 ^ 70 +
        2825844167559723858717352834369314475526826701242478581395198986490897) * 10 ^ 70 +
        9111915251075557239346554535217244968945589274361079502824189068316236) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 157 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 16 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (276 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_276 :
    recurrence2Scalar0Left.coeff 276 =
      (((311953769888266717133300312880622221358979216120033546749456228688489 * 10 ^ 70 +
        9721868198841977281103232117789238207662147268581806733309198405599598) * 10 ^ 70 +
        4600218922106635198960672337683828752840774010793680268285433633537554) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 158 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 15 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (277 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_277 :
    recurrence2Scalar0Left.coeff 277 =
      -(((145604581248372129381619097174984074101467606465638091826769590721689 * 10 ^ 70 +
        3797192685527994014666297973002772508096753184712444169456128688732871) * 10 ^ 70 +
        4533869322042505467665838865140965701294229549460938435873388524306128) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 159 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 14 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (278 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_278 :
    recurrence2Scalar0Left.coeff 278 =
      (((64006734341242971573020691212553763785200656311408521471859311376104 * 10 ^ 70 +
        7636917268309234555764647746149346845782535573508228470775219459523852) * 10 ^ 70 +
        1370681866570202555706120782731174577843065795856930746807278188233937) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 160 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 13 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (279 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_279 :
    recurrence2Scalar0Left.coeff 279 =
      -(((26369416302474511351507799104254305995526911339375450718953380176834 * 10 ^ 70 +
        8050965027275053892126978780966330284888869272195513267252847255652797) * 10 ^ 70 +
        4872057905454606650924758668974131977875806798581720041575477955011306) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 161 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 12 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (280 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_280 :
    recurrence2Scalar0Left.coeff 280 =
      (((10086711891390339920077093965227650973031601375697687021980663966832 * 10 ^ 70 +
        3679824095008349896677860651130069290721957809363774384034521942440470) * 10 ^ 70 +
        1726943141306280148977090409070307785304357254655653868039102570040003) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 162 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 11 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (281 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_281 :
    recurrence2Scalar0Left.coeff 281 =
      -(((3519748484627055095768347743771250178299193857037804603429867463316 * 10 ^ 70 +
        3600479441780084199044355162178208046835319063584174727280376096261081) * 10 ^ 70 +
        5388528927775369392029345893315811025085902481650597038498280950959153) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 163 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 10 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (282 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_282 :
    recurrence2Scalar0Left.coeff 282 =
      (((1079564085877134136770969200857389419543702890087135117669329494598 * 10 ^ 70 +
        3994995704634693134585616666041968822722891536559948176895701075157123) * 10 ^ 70 +
        2977656985923324800668053617843459097372538773691427373530574792497999) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 164 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 9 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (283 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_283 :
    recurrence2Scalar0Left.coeff 283 =
      -(((263407349636154058848024174954845820806096605734080797294367339365 * 10 ^ 70 +
        0358828971584518215005246681318474370274473470797337957460270767467073) * 10 ^ 70 +
        9726414431600482334250232463319815372090920348200837732816422799813515) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 165 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 8 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (284 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_284 :
    recurrence2Scalar0Left.coeff 284 =
      (((30477395520182675863173314172700607980131709412625236110904648376 * 10 ^ 70 +
        9453528230334060373206464628901078736616310632921364634827144350174375) * 10 ^ 70 +
        6185164879244600998232639461996524511233476735348217338586429131693608) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 166 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 7 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (285 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_285 :
    recurrence2Scalar0Left.coeff 285 =
      (((17301001199843862697122753753185309225845846040764394264551837662 * 10 ^ 70 +
        1463643938996787450565559357728472373257385089110771302473714140303069) * 10 ^ 70 +
        8726180028949937303965728033200161137867329557231723183065420837904417) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 167 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 6 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (286 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_286 :
    recurrence2Scalar0Left.coeff 286 =
      -(((17178154592780384995263386245904171311950444239699680178537572259 * 10 ^ 70 +
        9316905855897285114694359043321699864122207863729548760110261349162534) * 10 ^ 70 +
        0741609037285643861275651517238211121777994684764630993717032040306171) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 168 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 5 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (287 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_287 :
    recurrence2Scalar0Left.coeff 287 =
      (((9929703527666010513955196134848424719215732058742312559453652139 * 10 ^ 70 +
        8501870854585142984741227722937761363606319703729684523481924791616657) * 10 ^ 70 +
        4198996246133325109314828127139090780726229193933930614872989166376619) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 169 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 4 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (288 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_288 :
    recurrence2Scalar0Left.coeff 288 =
      -(((4680148133363474961997211967826477763828690585019665182648743952 * 10 ^ 70 +
        2958069516076104482459737242794818826452842131502657480430900719958591) * 10 ^ 70 +
        1756180130593807311497161030303000048943115505843025415782521113285235) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 170 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 3 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (289 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_289 :
    recurrence2Scalar0Left.coeff 289 =
      (((1944997934105728538010471746718170911670045678036382826887971743 * 10 ^ 70 +
        5605197981702689924245671749127317062397096122088164239722991498910932) * 10 ^ 70 +
        3136572094652376371825318827272624558507145216784776324963114039820573) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 171 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 2 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (290 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_290 :
    recurrence2Scalar0Left.coeff 290 =
      -(((733974574886567283077900970038059603252507567814467921908743824 * 10 ^ 70 +
        4598088488397049183758692173951119116045871647939563772836277581313346) * 10 ^ 70 +
        6023008680682286251052015128685199543778589581761868785663186648734075) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 172 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 1 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (291 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_291 :
    recurrence2Scalar0Left.coeff 291 =
      (((254671040299420473252495178406295913480499388825956404326428731 * 10 ^ 70 +
        0277829191620600663491553191309550832590235964768730460540089205196291) * 10 ^ 70 +
        6743069070973291825271960830522563365744187158973960327008399059907196) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 173 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (292 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_292 :
    recurrence2Scalar0Left.coeff 292 =
      -(((81593028949653090299866034502629908010596072809098621516484347 * 10 ^ 70 +
        4235361083892735971712049286861382970541326874488875887963307740167070) * 10 ^ 70 +
        5088174092510039228234285834119719614701688106158429250399919291039711) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 174 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 31 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (293 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_293 :
    recurrence2Scalar0Left.coeff 293 =
      (((24099865582317701899196595244657236865311351774654021109185409 * 10 ^ 70 +
        1161426052666246499008703608393744873149714184367335247388307852775161) * 10 ^ 70 +
        1372122921509347269764238450467642920353389514599383926638870079481522) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 175 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 30 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (294 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_294 :
    recurrence2Scalar0Left.coeff 294 =
      -(((6511268119406283556570911821032681462956199773902669157737105 * 10 ^ 70 +
        6204423726703066320956827341100612950129957839367757557122523854887345) * 10 ^ 70 +
        2559116678607310383987127538447596909498121763507280303923263712982883) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 176 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 29 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (295 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_295 :
    recurrence2Scalar0Left.coeff 295 =
      (((1580654746257439644443919563673819312185547511011936106076251 * 10 ^ 70 +
        1569772956402458362096886580260188916977815211694833241758592510542108) * 10 ^ 70 +
        0295591443438421904510907579306901619749681039557290483371590684779728) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 177 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 28 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (296 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_296 :
    recurrence2Scalar0Left.coeff 296 =
      -(((331029945764984283902876740017593313488025322745837495247407 * 10 ^ 70 +
        5810347991850608369416879990377150087226955480290847685141547831233701) * 10 ^ 70 +
        3300886977186647362142808193296730091399265234573658752635902628725133) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 178 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 27 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (297 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_297 :
    recurrence2Scalar0Left.coeff 297 =
      (((53235201465267518903977255810735019909806371275020274025191 * 10 ^ 70 +
        0757321405900022138948521080217856409933433231475855957302591591311996) * 10 ^ 70 +
        9581021324574030776883400171447750249557234727900379274136870254380688) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 179 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 26 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (298 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_298 :
    recurrence2Scalar0Left.coeff 298 =
      -(((3144252444646942809437028324978550170819889611939174197267 * 10 ^ 70 +
        8227152779465503228955897927920100772131683086339812668327556314807705) * 10 ^ 70 +
        0514594784511198645453156126703373395217459827166014661794231312074601) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 180 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 25 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (299 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_299 :
    recurrence2Scalar0Left.coeff 299 =
      -(((2135340135035202912181645658005876151606098910575241031048 * 10 ^ 70 +
        8170004846601639138482126294360114233377475617975484993367964998942700) * 10 ^ 70 +
        1340454750585403463442643755667416967612084589066305075191173228762343) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 181 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 24 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (300 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_300 :
    recurrence2Scalar0Left.coeff 300 =
      (((1251544805318809853230947841542476359110597053226510929139 * 10 ^ 70 +
        6886873745501200552744722063918126509985933575159379057608261737515614) * 10 ^ 70 +
        1507985777483217691506507464768312646015559320986927902591307392446966) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 182 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 23 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (301 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_301 :
    recurrence2Scalar0Left.coeff 301 =
      -(((460914529475600898770369276234329724132320295602413346367 * 10 ^ 70 +
        2593369833763846141073385747501955514893623153552107516024258283167516) * 10 ^ 70 +
        7806490062064021285844711533737746626794466390653387715711281021640599) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 183 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 22 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (302 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_302 :
    recurrence2Scalar0Left.coeff 302 =
      (((138698043645754278881576246606558675247446790829817256973 * 10 ^ 70 +
        7676897906665062201101388736327526771494000262715398013567347309998042) * 10 ^ 70 +
        8935931302483066777059142094589399047739821773599777636223530321105334) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 184 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 21 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (303 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_303 :
    recurrence2Scalar0Left.coeff 303 =
      -(((36427363813131744248262048830903457661905247974846635136 * 10 ^ 70 +
        4601364732214822671821400074219006239085754713868818563756923937420255) * 10 ^ 70 +
        1147075191421534125163470690953058167171167752367906414358826667584270) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 185 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 20 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (304 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_304 :
    recurrence2Scalar0Left.coeff 304 =
      (((8546289844532699754774555037218565003366421912907724017 * 10 ^ 70 +
        8572273030796796015276965771363676519539712119381456431008828160558337) * 10 ^ 70 +
        6226306101815808741416993102885078240328899728208249831605040498972924) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 186 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 19 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (305 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_305 :
    recurrence2Scalar0Left.coeff 305 =
      -(((1802065715256272371072915012567255154002194152199098112 * 10 ^ 70 +
        3791109807852338874292844782926255080085208076905512040090731638723422) * 10 ^ 70 +
        0472619162008011748183057405525381195706941987719780696080783017444144) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 187 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 18 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (306 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_306 :
    recurrence2Scalar0Left.coeff 306 =
      (((339576234181894497746640748401962167984182755241949111 * 10 ^ 70 +
        9278786117016098424958334722739143115901440960212919826995457537739060) * 10 ^ 70 +
        1990289632280803094435170298756234409135683294748808331470371343912314) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 188 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 17 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (307 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_307 :
    recurrence2Scalar0Left.coeff 307 =
      -(((55999465719470507113607681682008447769627324553804838 * 10 ^ 70 +
        3458190334696177197300579994073592997437452292701105387064469237687749) * 10 ^ 70 +
        2443264300692508884753670172850017388895572112465862361329445249860967) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 189 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 16 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (308 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_308 :
    recurrence2Scalar0Left.coeff 308 =
      (((7645668514833020598754661557393462628467566028802453 * 10 ^ 70 +
        5256693581058440136382079146189602425150172866526455282197333275134487) * 10 ^ 70 +
        7973620951444016533721786968440049924114116485174073027843745851281344) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 190 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 15 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
