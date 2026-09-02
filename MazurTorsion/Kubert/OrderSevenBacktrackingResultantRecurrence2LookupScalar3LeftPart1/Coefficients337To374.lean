/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Left coefficient convolution

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
  recurrence2A3_coeff_0
  recurrence2A3_coeff_1
  recurrence2A3_coeff_2
  recurrence2A3_coeff_3
  recurrence2A3_coeff_4
  recurrence2A3_coeff_5
  recurrence2A3_coeff_6
  recurrence2A3_coeff_7
  recurrence2A3_coeff_8
  recurrence2A3_coeff_9
  recurrence2A3_coeff_10
  recurrence2A3_coeff_11
  recurrence2A3_coeff_12
  recurrence2A3_coeff_13
  recurrence2A3_coeff_14
  recurrence2A3_coeff_15
  recurrence2A3_coeff_16
  recurrence2A3_coeff_17
  recurrence2A3_coeff_18
  recurrence2A3_coeff_19
  recurrence2A3_coeff_20
  recurrence2A3_coeff_21
  recurrence2A3_coeff_22
  recurrence2A3_coeff_23
  recurrence2A3_coeff_24
  recurrence2A3_coeff_25
  recurrence2A3_coeff_26
  recurrence2A3_coeff_27
  recurrence2A3_coeff_28
  recurrence2A3_coeff_29
  recurrence2A3_coeff_30
  recurrence2A3_coeff_31
  recurrence2A3_coeff_32
  recurrence2A3_coeff_33
  recurrence2A3_coeff_34
  recurrence2A3_coeff_35
  recurrence2A3_coeff_36
  recurrence2A3_coeff_37
  recurrence2A3_coeff_38
  recurrence2A3_coeff_39
  recurrence2A3_coeff_40
  recurrence2A3_coeff_41
  recurrence2A3_coeff_42
  recurrence2A3_coeff_43
  recurrence2A3_coeff_44
  recurrence2A3_coeff_45
  recurrence2A3_coeff_46
  recurrence2A3_coeff_47
  recurrence2A3_coeff_48
  recurrence2A3_coeff_49
  recurrence2A3_coeff_50
  recurrence2A3_coeff_51
  recurrence2A3_coeff_52
  recurrence2A3_coeff_53
  recurrence2A3_coeff_54
  recurrence2A3_coeff_55
  recurrence2A3_coeff_56
  recurrence2A3_coeff_57
  recurrence2A3_coeff_58
  recurrence2A3_coeff_59
  recurrence2A3_coeff_60
  recurrence2A3_coeff_61
  recurrence2A3_coeff_62
  recurrence2A3_coeff_63
  recurrence2A3_coeff_64
  recurrence2A3_coeff_65
  recurrence2A3_coeff_66
  recurrence2A3_coeff_67
  recurrence2A3_coeff_68
  recurrence2A3_coeff_69
  recurrence2A3_coeff_70
  recurrence2A3_coeff_71
  recurrence2A3_coeff_72
  recurrence2A3_coeff_73
  recurrence2A3_coeff_74
  recurrence2A3_coeff_75
  recurrence2A3_coeff_76
  recurrence2A3_coeff_77
  recurrence2A3_coeff_78
  recurrence2A3_coeff_79
  recurrence2A3_coeff_80
  recurrence2A3_coeff_81
  recurrence2A3_coeff_82
  recurrence2A3_coeff_83
  recurrence2A3_coeff_84
  recurrence2A3_coeff_85
  recurrence2A3_coeff_86
  recurrence2A3_coeff_87
  recurrence2A3_coeff_88
  recurrence2A3_coeff_89
  recurrence2A3_coeff_90
  recurrence2A3_coeff_91
  recurrence2A3_coeff_92
  recurrence2A3_coeff_93
  recurrence2A3_coeff_94
  recurrence2A3_coeff_95
  recurrence2A3_coeff_96
  recurrence2A3_coeff_97
  recurrence2A3_coeff_98
  recurrence2A3_coeff_99
  recurrence2A3_coeff_100
  recurrence2A3_coeff_101
  recurrence2A3_coeff_102
  recurrence2A3_coeff_103
  recurrence2A3_coeff_104
  recurrence2A3_coeff_105
  recurrence2A3_coeff_106

private theorem recurrence2Scalar3Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (337 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_337 :
    recurrence2Scalar3Left.coeff 337 =
      (((1713412113 * 10 ^ 70 +
        2380170548139694638702910527328266194385444866262321257907713242943324) * 10 ^ 70 +
        1176578964398111909832111373453225374233292318941362434491374556004473) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 231 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 6 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (338 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_338 :
    recurrence2Scalar3Left.coeff 338 =
      (((2830769 * 10 ^ 70 +
        3204197992827768762447652568029224727183642082762927369940402906073459) * 10 ^ 70 +
        5347004513188700170839093724472724652078635037619166044986399959381779) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 232 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 5 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (339 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_339 :
    recurrence2Scalar3Left.coeff 339 =
      -(((423224 * 10 ^ 70 +
        3619611735297800503461487013000196057934378448975250645850042328361734) * 10 ^ 70 +
        2862663821259137379082165324372427701850404846722047483080130726350540) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 233 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 4 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (340 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_340 :
    recurrence2Scalar3Left.coeff 340 =
      (((4600 * 10 ^ 70 +
        7011527543347161581512729318554051989650382928325655747115905070466506) * 10 ^ 70 +
        9811886634516903482399473854853856596579341180770689403235222781887118) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 234 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 3 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (341 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_341 :
    recurrence2Scalar3Left.coeff 341 =
      (((11 * 10 ^ 70 +
        8304126432707249631195155017327352625264606472194104576412265482521704) * 10 ^ 70 +
        5920128949330098077949732051185503280004230574531108515388209491262757) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 235 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 2 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (342 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_342 :
    recurrence2Scalar3Left.coeff 342 =
      -((5405837252171348042979984183340999502644009082701875918709057825296547 * 10 ^ 70 +
        4714278453950929310708905943729938927844759644496409026290024486766840) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 236 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 1 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (343 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_343 :
    recurrence2Scalar3Left.coeff 343 =
      ((19738513681865029371806025083338685527731129477019435220950292866652 * 10 ^ 70 +
        2782591823317053660619477001870636207040662627702903656048164357206995) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 237 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (344 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_344 :
    recurrence2Scalar3Left.coeff 344 =
      ((248752319861657634491590027160208225404930745796658523890791681871 * 10 ^ 70 +
        0297116908409518092170981606274481296163435209241249928644790665475297) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 238 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 31 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (345 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_345 :
    recurrence2Scalar3Left.coeff 345 =
      -((1723920327064793341056660867294972846011007182122515942892057768 * 10 ^ 70 +
        1374317909948923902298579048839467486363673220655862397466089562351464) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 239 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 30 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (346 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_346 :
    recurrence2Scalar3Left.coeff 346 =
      -((5088454320232556029484271482919170587038036499858951675855533 * 10 ^ 70 +
        6876379295228149411906500253180207331651255946786124587931067162727316) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 240 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 29 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (347 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_347 :
    recurrence2Scalar3Left.coeff 347 =
      ((60829493402318203930589243795817633336875492242596277454790 * 10 ^ 70 +
        1812905255037096034999435992086991095542260333613045930374043919862726) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 241 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 28 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (348 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_348 :
    recurrence2Scalar3Left.coeff 348 =
      ((16238836400748776325926586579350938327505718238027781887 * 10 ^ 70 +
        8153419721209160483045359014146297946649206033695820350985702362045845) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 242 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 27 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (349 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_349 :
    recurrence2Scalar3Left.coeff 349 =
      -((1128215886770036836912455109308525500590182993664748125 * 10 ^ 70 +
        7842322474704604551151887025506198322523132259789780587706408001164676) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 243 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 26 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (350 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_350 :
    recurrence2Scalar3Left.coeff 350 =
      ((1295076570859286081552224863333775937444769359461597 * 10 ^ 70 +
        3427301611495838354690533251702382179651347740965243978760592746831993) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 244 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 25 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (351 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_351 :
    recurrence2Scalar3Left.coeff 351 =
      ((11004841822322302368302871260521898405192552565524 * 10 ^ 70 +
        0493738334654212575138164189170273463331396220676231252119589794400570) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 245 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 24 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (352 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_352 :
    recurrence2Scalar3Left.coeff 352 =
      -((25427159667199743460741496963082870124331345052 * 10 ^ 70 +
        7058021020249893838727978428014520095871206801079234391386913849611504) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 246 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 23 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (353 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_353 :
    recurrence2Scalar3Left.coeff 353 =
      -((43736786144096067401321081860530861199169085 * 10 ^ 70 +
        2007184910360237826283753177684185516841987137798045954103565034117775) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 247 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 22 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (354 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_354 :
    recurrence2Scalar3Left.coeff 354 =
      ((192050527178511654926347789943707017487536 * 10 ^ 70 +
        3130755792309929484597401350143872703656456515627652767513105720199103) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 248 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 21 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (355 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_355 :
    recurrence2Scalar3Left.coeff 355 =
      -((68100958374523921820822546928838047823 * 10 ^ 70 +
        8558091592471827353905107802238178606566727110652939772158280986330628) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 249 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 20 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (356 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_356 :
    recurrence2Scalar3Left.coeff 356 =
      -((499531830966420261029331335531570896 * 10 ^ 70 +
        7934384823400964888651419790183774432626495282453070965227052907098196) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 250 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 19 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (357 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_357 :
    recurrence2Scalar3Left.coeff 357 =
      ((791047997498558552571917798559726 * 10 ^ 70 +
        9249192091405279765699677116162123108867295392231128005886037608390571) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 251 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 18 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (358 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_358 :
    recurrence2Scalar3Left.coeff 358 =
      -((248452242912370909206071832202 * 10 ^ 70 +
        9672440219885300245896774930179462670673983075801130612468305981432545) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 252 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 17 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (359 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_359 :
    recurrence2Scalar3Left.coeff 359 =
      -((388293726068666152816049677 * 10 ^ 70 +
        8418052244824442813621652295495081539833126932337847431126844504775235) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 253 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 16 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (360 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_360 :
    recurrence2Scalar3Left.coeff 360 =
      ((404397741696115078246667 * 10 ^ 70 +
        7913941072483337550811594821878005252062236656863367558357015302452374) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 254 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 15 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (361 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_361 :
    recurrence2Scalar3Left.coeff 361 =
      -((140475978139930382982 * 10 ^ 70 +
        7888807441890036080978230430467841539741556673033100691253781423032345) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 255 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 14 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (362 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_362 :
    recurrence2Scalar3Left.coeff 362 =
      ((12351359454808699 * 10 ^ 70 +
        3578226148894827097326566064895119289089816936186691413164145351153783) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 256 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 13 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (363 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_363 :
    recurrence2Scalar3Left.coeff 363 =
      ((3160881795291 * 10 ^ 70 +
        3581448363262346312735596755610485598424394185273730368799612913819151) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 257 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 12 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (364 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_364 :
    recurrence2Scalar3Left.coeff 364 =
      -((732774502 * 10 ^ 70 +
        8586495626094457694580250091407758313113403185049071760062253720554657) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 258 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 11 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (365 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_365 :
    recurrence2Scalar3Left.coeff 365 =
      ((47762 * 10 ^ 70 +
        0808211605104521592343781990483756619150576160789972041968293854581033) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 259 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 10 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (366 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_366 :
    recurrence2Scalar3Left.coeff 366 =
      (-9454948867434608337668196268082805373340226918649820558566057715237343 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 260 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 9 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (367 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_367 :
    recurrence2Scalar3Left.coeff 367 =
      (-65868902530199323065629140195009959460502941916682889267898432408 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 261 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 8 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (368 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_368 :
    recurrence2Scalar3Left.coeff 368 =
      (2443822343223082194782832322743060621912073396130668310433814 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 262 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 7 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (369 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_369 :
    recurrence2Scalar3Left.coeff 369 =
      (-14202745730161737235415289213336709812151430136454293417 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 263 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 6 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (370 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_370 :
    recurrence2Scalar3Left.coeff 370 =
      (15742905152230615934102356088409185682380339195076 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 264 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 5 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (371 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_371 :
    recurrence2Scalar3Left.coeff 371 =
      (-2995791125347133595513127658029915158440732 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 265 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 4 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (372 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_372 :
    recurrence2Scalar3Left.coeff 372 =
      (-1410347095972451960882153638879833503 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 266 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 3 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (373 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_373 :
    recurrence2Scalar3Left.coeff 373 =
      (19718337189424179550878922270 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 267 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 2 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (374 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_374 :
    recurrence2Scalar3Left.coeff 374 =
      (-67965145443184571654 : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 268 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 1 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
