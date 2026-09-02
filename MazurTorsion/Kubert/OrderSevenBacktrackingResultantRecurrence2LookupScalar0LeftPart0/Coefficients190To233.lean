/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0LeftPart0Simp
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

private theorem recurrence2Scalar0Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_190 :
    recurrence2Scalar0Left.coeff 190 =
      (((1701517308676765193753316741372236665633160154220180082810597 * 10 ^ 70 +
        6406448324088008822744116556250708989559406843121310923061423011939881) * 10 ^ 70 +
        6276826506820568610813196669468682710610595649430505387921143652458128) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 72 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_190_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_191 :
    recurrence2Scalar0Left.coeff 191 =
      -(((5544868299555822703078423125708931907099161102883844544793953 * 10 ^ 70 +
        4846053618600600075000554918970703408849971473413720402267588267858409) * 10 ^ 70 +
        7306611193983272483064598148756878821826715950081958906080715978546417) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 73 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_191_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_192 :
    recurrence2Scalar0Left.coeff 192 =
      (((9557005957323545364834166028379990851137585486404570171039724 * 10 ^ 70 +
        2977117044099651918302420740155042681498551319479146871298358803979556) * 10 ^ 70 +
        3924042098134997169845477097951919955258705194964635775842816434818966) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 74 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_192_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_193 :
    recurrence2Scalar0Left.coeff 193 =
      (((1279830782940325012887157533052326091324664391526750812119065 * 10 ^ 70 +
        9348690072783913765540932918985085035450257760175436664978131816075905) * 10 ^ 70 +
        2555863608778327134905698087238774863179945915497292598647751315079015) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 75 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_193_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_194 :
    recurrence2Scalar0Left.coeff 194 =
      -(((70156543125385864115181070631846541223979222163311892168315261 * 10 ^ 70 +
        1512825015170989963316030657681187461696581926753337823598516336174192) * 10 ^ 70 +
        5697842126763683160810128210238561057260832543255843064091826749307406) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 76 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_194_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_195 :
    recurrence2Scalar0Left.coeff 195 =
      (((264769395522459524285504438516930671225042679435260403263110976 * 10 ^ 70 +
        8454322203805654647943584378466138173836447383505899506416391943999737) * 10 ^ 70 +
        8602126816419580235342550214494849020797134954324382691327714331692040) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 77 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_195_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_196 :
    recurrence2Scalar0Left.coeff 196 =
      -(((570296758502546521869573498809143585506235287473002972753037881 * 10 ^ 70 +
        9005653768623105399397749686874367595467014133387844801258614158495346) * 10 ^ 70 +
        6329876505235671989737499872712050641150837720358597222044172689853616) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 78 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_196_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_197 :
    recurrence2Scalar0Left.coeff 197 =
      (((512424412203222947319546244105304554940291942286162115097949317 * 10 ^ 70 +
        9908029799603665826253614483075958873396556891161816182903693760986677) * 10 ^ 70 +
        3937586662535110525178891652277777240935157746563218081457293080950974) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 79 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_197_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_198 :
    recurrence2Scalar0Left.coeff 198 =
      (((1619646159988969942312193000224012651491263421637920919163801796 * 10 ^ 70 +
        2489856794774297394924701499524629823550747970033627258531796361072528) * 10 ^ 70 +
        1900201828480752864800824854760800250265242836784753932676315841399108) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 80 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_198_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_199 :
    recurrence2Scalar0Left.coeff 199 =
      -(((9503091682700078879845535868810954209062109726699335585077355573 * 10 ^ 70 +
        3202661762501903109615301489936109517054506474926466542967305409139668) * 10 ^ 70 +
        8488560852212987366760445120765326501663957464523145876119997050025587) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 81 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_199_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_200 :
    recurrence2Scalar0Left.coeff 200 =
      (((27138781698737607272747113877674878832307413350659261541508918532 * 10 ^ 70 +
        8627211567171668085653710784291723926594204761172766015269499239255656) * 10 ^ 70 +
        3582227240305657194405142468102461362820984443868892342023179180974615) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 82 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_200_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_201 :
    recurrence2Scalar0Left.coeff 201 =
      -(((48764039017046358994654824472181062376316268574376483990763516881 * 10 ^ 70 +
        2044391250784127976578973620473555145263822275996926779852600967098558) * 10 ^ 70 +
        4224652667185056586170040270119388229253680837202802073394236656599100) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 83 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_201_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_202 :
    recurrence2Scalar0Left.coeff 202 =
      (((30315100666502719347097131065773603331823839885881372182031738870 * 10 ^ 70 +
        0642294929801837851615551086887396045051564612177848329940631006834322) * 10 ^ 70 +
        7327938449927234890554595702477059436644577937324816255535244167323688) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 84 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_202_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_203 :
    recurrence2Scalar0Left.coeff 203 =
      (((163251202319181122949185318238981051844036659144591648302228467933 * 10 ^ 70 +
        4193402076535788117622373973949421620792802344835116367091740944087157) * 10 ^ 70 +
        3254431205701486170566700453307351654357268791365272567615646587463571) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 85 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_203_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_204 :
    recurrence2Scalar0Left.coeff 204 =
      -(((806545341234020715522435133480237914400565442100586755288974014583 * 10 ^ 70 +
        8553967769124288921235429619356876061080835493456509637254997222176183) * 10 ^ 70 +
        3963984624460022578226014307728218166485173226327598250769502032127940) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 86 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_204_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_205 :
    recurrence2Scalar0Left.coeff 205 =
      (((2230497004188147931301863973927709473361724129830955694029895814887 * 10 ^ 70 +
        5509839084137565731246543120649117565210811329368206378081116100546280) * 10 ^ 70 +
        7859599948010595530116715813488936405751641068419227677496650414147971) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 87 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_205_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_206 :
    recurrence2Scalar0Left.coeff 206 =
      -(((4282594824601090108213484166123968309646830523445811311865151575218 * 10 ^ 70 +
        2255455897087710646564232327963085858907166819182194065896711821333087) * 10 ^ 70 +
        6029597725276867468126381736527325057238619556075849703239046238217423) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 88 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_206_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_207 :
    recurrence2Scalar0Left.coeff 207 =
      (((4750600971271682256647906567782418905293423026562415275059775348649 * 10 ^ 70 +
        9411038019564671436564507539938956433856856346215423939648096549641354) * 10 ^ 70 +
        2523829815535438806551772975708804771674362688019927155174688037474660) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 89 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_207_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_208 :
    recurrence2Scalar0Left.coeff 208 =
      (((3891430787680910053291971180072546912039468912810775527638555241802 * 10 ^ 70 +
        7274485997417936899907007758192584081681509301033058245105407246629012) * 10 ^ 70 +
        8441974314942601071070880440768999474547549402817750460968742321231223) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 90 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_208_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_209 :
    recurrence2Scalar0Left.coeff 209 =
      -(((39242337338871663520851187010417630734735193433903387144384972681259 * 10 ^ 70 +
        0324666473199870840772176488287655977681294618041487721376779164982566) * 10 ^ 70 +
        0712121407263169173151603167397082591183071397860141148515856867204419) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 91 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_209_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_210 :
    recurrence2Scalar0Left.coeff 210 =
      (((132078687457299276201664791627940608226312129729641800509670202695202 * 10 ^ 70 +
        8768311608275077674960722995467745877296484324091744771488280493613101) * 10 ^ 70 +
        6010471256477454504457652357286330622500538566065778086051148947704365) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 92 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_210_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_211 :
    recurrence2Scalar0Left.coeff 211 =
      -(((317657280168411377696979604180899097028037834959856701492801915072119 * 10 ^ 70 +
        8186861875653298569682697876086698979950929575695691272523760745642776) * 10 ^ 70 +
        1019772650712235643765427871248879310190651186186321339824281078965788) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 93 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_211_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_212 :
    recurrence2Scalar0Left.coeff 212 =
      (((592507368061864329972780813202346962896838738456816953604067056032488 * 10 ^ 70 +
        9083256497954192623396746853047159265883672972985683659572375771395994) * 10 ^ 70 +
        3591537935464960423064627688525730617681595089301660379313717609113837) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 94 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_212_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_213 :
    recurrence2Scalar0Left.coeff 213 =
      -(((796493957704085514063312872179562410751786562580412215209657472228326 * 10 ^ 70 +
        7227203338105043980050021604553673021433582140592791640882558409606115) * 10 ^ 70 +
        8974436856173971248060199107378213326850335142084654095250368719309380) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 95 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_213_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_214 :
    recurrence2Scalar0Left.coeff 214 =
      (((363455832946510987563227666782933269337259020745692311999051353235212 * 10 ^ 70 +
        3842899005581878288124922245238542672368943956195237837658918489177640) * 10 ^ 70 +
        6880851976729738827469159520227569869567220796938434417728567217128907) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 96 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_214_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_215 :
    recurrence2Scalar0Left.coeff 215 =
      (((2116804248656792684804634158244525469159349484333139781308347745189840 * 10 ^ 70 +
        1887103804616429515743817275039553344300391550055599866360198699247122) * 10 ^ 70 +
        3826808634922393772558140204680636417980356704546894180405293630023440) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 97 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_215_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_216 :
    recurrence2Scalar0Left.coeff 216 =
      -(((9541451835844092587733882197599862774622558748281086832547727260663006 * 10 ^ 70 +
        1830939020642344655540044449583088240828628863322744989665825026202183) * 10 ^ 70 +
        5467765978468220924647203755922044856817619219593642208999538425675461) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 98 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_216_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_217 :
    recurrence2Scalar0Left.coeff 217 =
      ((((2 * 10 ^ 70 +
        7044135820817024951437881433429029313351894896150457102226716936197847) * 10 ^ 70 +
        2872027788566750192011334016183470322287117848979867753458787985467032) * 10 ^ 70 +
        2883939766394769144972226128100969963359537115153629457810500037929204) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 99 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_217_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_218 :
    recurrence2Scalar0Left.coeff 218 =
      -((((6 * 10 ^ 70 +
        2538967022145510168109698623188947562771505231877207763200103310699821) * 10 ^ 70 +
        7254526744689946973827571411598172872471535309756365381214623355987912) * 10 ^ 70 +
        8031778066018822692493377514949227104280730278853296559250001528194700) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 100 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_218_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_219 :
    recurrence2Scalar0Left.coeff 219 =
      ((((12 * 10 ^ 70 +
        6439066559634354381643357025201275628401602869972774832980343601557316) * 10 ^ 70 +
        1007630953376977256034995818722579837311961306055108749812144308223932) * 10 ^ 70 +
        0790325532206724645467868157299655043596703339099972335086392974600943) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 101 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_219_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_220 :
    recurrence2Scalar0Left.coeff 220 =
      -((((22 * 10 ^ 70 +
        9593397277938821408372885878909744549120431526016349331026704079571640) * 10 ^ 70 +
        5226202323373365858667019736247193873544031906964205059100793790106605) * 10 ^ 70 +
        8935851345538718153825818189182307628806517293266881170128906276114720) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 102 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_220_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_221 :
    recurrence2Scalar0Left.coeff 221 =
      ((((37 * 10 ^ 70 +
        8267552459968374269772645600321360101517654106793564236572692571913239) * 10 ^ 70 +
        2153605070009731384040857142592923602444278644722124503698592318718506) * 10 ^ 70 +
        5610236233578559387454568301105037735556492213369770198239958471106121) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 103 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_221_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_222 :
    recurrence2Scalar0Left.coeff 222 =
      -((((56 * 10 ^ 70 +
        5115522023834762706928189935890975114478309280418445404061877891295717) * 10 ^ 70 +
        6111674032579849204642255949450278801196665529724110905793854115193665) * 10 ^ 70 +
        6578141720257092627516207142005528419592781074150492018764729237746511) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 104 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_222_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_223 :
    recurrence2Scalar0Left.coeff 223 =
      ((((75 * 10 ^ 70 +
        5788857841803406815094362724857935095871937029356898037589965908484897) * 10 ^ 70 +
        9791243473302455982995212074979446373521530819427135889984744277721704) * 10 ^ 70 +
        2455899825096988200110235121622580255238126116317463085097462800583433) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 105 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_223_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_224 :
    recurrence2Scalar0Left.coeff 224 =
      -((((87 * 10 ^ 70 +
        2252601178224516683791182117025752392322038267845586853730131816795954) * 10 ^ 70 +
        6239402439175196515020223049911897678141193640623407672761787286058663) * 10 ^ 70 +
        3533746790446629081543299504811048213844640988271312220934344034557626) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 106 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_224_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_225 :
    recurrence2Scalar0Left.coeff 225 =
      ((((77 * 10 ^ 70 +
        5933970459629068124391641133230690045664948027761473621385905605608423) * 10 ^ 70 +
        0820374381418108876804160339443248774109891680409470699480578366631333) * 10 ^ 70 +
        4492504084706361523136760326267080908266598287439055986158053354809460) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 107 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_225_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_226 :
    recurrence2Scalar0Left.coeff 226 =
      -((((25 * 10 ^ 70 +
        6078765678855760316903805833517222199592482022201197556891965357478239) * 10 ^ 70 +
        4856396752944122265638994615626592619282238685672018630116686390950377) * 10 ^ 70 +
        2482220323534478922965575121673542680887134260835806384575757595379155) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 108 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_226_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_227 :
    recurrence2Scalar0Left.coeff 227 =
      -((((96 * 10 ^ 70 +
        9672335848135629808973365613658675674550832190505447572272273101558597) * 10 ^ 70 +
        2002323362416336123628062538362326553015654272918948561204724099574884) * 10 ^ 70 +
        2481305220527340233318669723209519864424253838941962974760874252312427) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 109 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_227_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_228 :
    recurrence2Scalar0Left.coeff 228 =
      ((((323 * 10 ^ 70 +
        5455236196444214141336960289887478103169806197263977572188522437501220) * 10 ^ 70 +
        2708602200311742478065731794013070694851071409622085750347106641193103) * 10 ^ 70 +
        3147548118994668513185999589937135169640695726581175477458449020466808) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 110 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_228_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_229 :
    recurrence2Scalar0Left.coeff 229 =
      -((((688 * 10 ^ 70 +
        3527544010698873146446839329449541016148676408327895051812226463141390) * 10 ^ 70 +
        7377824595056902279449879862548303639739699299538419526099192607620772) * 10 ^ 70 +
        3505480007671372763170495730495760255996154324962457147401192675362545) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 111 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_229_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_230 :
    recurrence2Scalar0Left.coeff 230 =
      ((((1219 * 10 ^ 70 +
        7419526163393054100994545924863133909665046406691137468299765657490839) * 10 ^ 70 +
        1425349410289736673592351578750103848230050045420755000443436093469486) * 10 ^ 70 +
        7114193092879645308099915952281151367366237942141242330527243932096521) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 112 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_230_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_231 :
    recurrence2Scalar0Left.coeff 231 =
      -((((1931 * 10 ^ 70 +
        9775546199862715335397206451426967290921095837748401886624315553455355) * 10 ^ 70 +
        7391863225633775954815515130308057786938974087611176498508034126784888) * 10 ^ 70 +
        5525491545145358620412572371296318087315445764986559710682706704890877) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 113 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_231_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_232 :
    recurrence2Scalar0Left.coeff 232 =
      ((((2817 * 10 ^ 70 +
        0295988667402145721133453559724266025637888333223370638165956989557103) * 10 ^ 70 +
        1793328846238727297403246826310031669758245036921154799111576811976745) * 10 ^ 70 +
        9538032718439120805954595066231922091102430838900965664670109452785504) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 114 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_232_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_233 :
    recurrence2Scalar0Left.coeff 233 =
      -((((3838 * 10 ^ 70 +
        4473875757736270753572497429931642432635553434969966129468827882439523) * 10 ^ 70 +
        7006520366616814875305280399077999738160109802704220770274855678829554) * 10 ^ 70 +
        8014929305181892644324637583076989670010561039310912891955441182760584) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 115 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_233_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
