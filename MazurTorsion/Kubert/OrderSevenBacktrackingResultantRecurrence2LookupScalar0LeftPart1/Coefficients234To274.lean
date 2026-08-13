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

private theorem recurrence2Scalar0Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_234 :
    recurrence2Scalar0Left.coeff 234 =
      ((((4929 * 10 ^ 70 +
        4368763111948477564623652883427472539906252987824530197655159639292167) * 10 ^ 70 +
        4723347423850374756525799724198083278380204323390561374079328792415556) * 10 ^ 70 +
        0462834058432437692870061017674433994485750282708389222249437167571895) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 116 +
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
  rw [recurrence2Scalar0Left_coeff_234_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_235 :
    recurrence2Scalar0Left.coeff 235 =
      -((((5996 * 10 ^ 70 +
        6977061973196494020648598631760716219647648148910832325458377760899128) * 10 ^ 70 +
        3321120918098098170785333525028586722865637600667054874053298466307762) * 10 ^ 70 +
        1446605391774386324176876098003674756168190973018421466158022504206776) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 117 +
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
  rw [recurrence2Scalar0Left_coeff_235_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_236 :
    recurrence2Scalar0Left.coeff 236 =
      ((((6930 * 10 ^ 70 +
        4173725644434093377934984218387992518864583682475455347452554240647595) * 10 ^ 70 +
        2913875908556347629190531978811799354851121672774922709218433480660274) * 10 ^ 70 +
        9797892035643644368341904718171804639373514315984916341111702913728630) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 118 +
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
  rw [recurrence2Scalar0Left_coeff_236_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_237 :
    recurrence2Scalar0Left.coeff 237 =
      -((((7619 * 10 ^ 70 +
        3156750022859454028617423486426721573657186802557410683278606324095371) * 10 ^ 70 +
        5025454469250983337675775842195528943834569898994658123691077754163785) * 10 ^ 70 +
        7447546369082922804303657028114412417126034065870118149154359129547633) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 119 +
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
  rw [recurrence2Scalar0Left_coeff_237_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_238 :
    recurrence2Scalar0Left.coeff 238 =
      ((((7968 * 10 ^ 70 +
        1880087458833251933434356029990104579277964385354813921781316390738492) * 10 ^ 70 +
        7117899063197885782105513261951522763992900222450550748242227358562108) * 10 ^ 70 +
        8601214842977552720241830451836479820200358214318623386678929888183408) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 120 +
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
  rw [recurrence2Scalar0Left_coeff_238_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_239 :
    recurrence2Scalar0Left.coeff 239 =
      -((((7914 * 10 ^ 70 +
        4579601491536353690409402823522031065878216343945021978828615497878893) * 10 ^ 70 +
        2628611319015013767805694155581592416371323457386518194582916828540507) * 10 ^ 70 +
        1679674180242769779594549038556518788625117037592438274515011294646467) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 121 +
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
  rw [recurrence2Scalar0Left_coeff_239_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_240 :
    recurrence2Scalar0Left.coeff 240 =
      ((((7440 * 10 ^ 70 +
        1531600140252977098672524225268933895009020988902382617439820787588005) * 10 ^ 70 +
        3515258234629813572894824042965365478687499315605340575971802438230340) * 10 ^ 70 +
        9926165485786480292809286836978751248520824599297184513659226923539722) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 122 +
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
  rw [recurrence2Scalar0Left_coeff_240_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_241 :
    recurrence2Scalar0Left.coeff 241 =
      -((((6576 * 10 ^ 70 +
        5596743072319112132491041451353012326602805927834141194797709853327611) * 10 ^ 70 +
        1588595755590083957037339667442774388004397702234824140724959073222047) * 10 ^ 70 +
        7056522979514152532995187857767416501351861492865749998208869540139834) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 123 +
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
  rw [recurrence2Scalar0Left_coeff_241_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_242 :
    recurrence2Scalar0Left.coeff 242 =
      ((((5400 * 10 ^ 70 +
        3974574837296978424173052948150174477223275689647975110079880506033330) * 10 ^ 70 +
        4469320854423448871944680671115300796585549521839774065418887044419813) * 10 ^ 70 +
        6289271501175365561626957049857954772305399635348568786881019395244174) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 124 +
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
  rw [recurrence2Scalar0Left_coeff_242_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_243 :
    recurrence2Scalar0Left.coeff 243 =
      -((((4022 * 10 ^ 70 +
        2649343519677550496215520520209674807662439199579509090647415843502804) * 10 ^ 70 +
        3676448424698232334008444029110742958437766135747329418121331561153532) * 10 ^ 70 +
        9392581476192792520441575114266330889383843207066988403996445854046548) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 125 +
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
  rw [recurrence2Scalar0Left_coeff_243_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_244 :
    recurrence2Scalar0Left.coeff 244 =
      ((((2569 * 10 ^ 70 +
        7987712086342863312884243597302523586715564044056913162084207072657530) * 10 ^ 70 +
        0666446821642581490865721055327707300953334460661771889130048931473876) * 10 ^ 70 +
        1738157900982976726242063969344055721401935199216281957842552573077768) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 126 +
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
  rw [recurrence2Scalar0Left_coeff_244_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_245 :
    recurrence2Scalar0Left.coeff 245 =
      -((((1169 * 10 ^ 70 +
        0326239843355881961925454284948122198179318509435574286421753069268158) * 10 ^ 70 +
        2178546857498607332730402565177283245745933980412824501988486086345676) * 10 ^ 70 +
        6502704478585565570078608176464366073668701370100040259403801854599156) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 127 +
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
  rw [recurrence2Scalar0Left_coeff_245_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_246 :
    recurrence2Scalar0Left.coeff 246 =
      -((((72 * 10 ^ 70 +
        4224285428885341381177490558898948948915691092422610677696234848279942) * 10 ^ 70 +
        5735699427828694211258876787636862270030227824870592881396070259864853) * 10 ^ 70 +
        3799100277314282122316486693995192474098420055691159253353293945585865) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 128 +
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
  rw [recurrence2Scalar0Left_coeff_246_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_247 :
    recurrence2Scalar0Left.coeff 247 =
      ((((1077 * 10 ^ 70 +
        4765492552742860857687453463160184464018618692603795749458808157619809) * 10 ^ 70 +
        5168240644855686682478618867366746178292005923929688963987780456600181) * 10 ^ 70 +
        0646333358105099612415691258591062445145225439481690099544699527374861) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 129 +
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
  rw [recurrence2Scalar0Left_coeff_247_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_248 :
    recurrence2Scalar0Left.coeff 248 =
      -((((1805 * 10 ^ 70 +
        3499657765882533444209160655476484984619606495038735408437333918098099) * 10 ^ 70 +
        1541870550590704141966572971945054852283473460740573805631442884734219) * 10 ^ 70 +
        3462371448782739772040217203354104521953466454993513976566376486433329) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 130 +
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
  rw [recurrence2Scalar0Left_coeff_248_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_249 :
    recurrence2Scalar0Left.coeff 249 =
      ((((2250 * 10 ^ 70 +
        9556144096365727931409585298052971477010557761417048160895646982048251) * 10 ^ 70 +
        9536359394334644311292356309843160540934793395759993048667461857649275) * 10 ^ 70 +
        5801382343625894976464857131595435720597407453153222143117520183192471) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 131 +
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
  rw [recurrence2Scalar0Left_coeff_249_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_250 :
    recurrence2Scalar0Left.coeff 250 =
      -((((2439 * 10 ^ 70 +
        0586590698320063724990476570895130252117377226030756509158230879132800) * 10 ^ 70 +
        3445975190824361941313549963371333859505907174757644415181500221606938) * 10 ^ 70 +
        4031991205993291450699301696695800747998397000580407276074293246014821) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 132 +
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
  rw [recurrence2Scalar0Left_coeff_250_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_251 :
    recurrence2Scalar0Left.coeff 251 =
      ((((2415 * 10 ^ 70 +
        1895545828723112503820878698117912546377937268575505453907309345194924) * 10 ^ 70 +
        4767730817532985415409994685740814730579202337365118610426944569789882) * 10 ^ 70 +
        7961955199517610591890644198388563979431517183913383519656508831384895) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 133 +
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
  rw [recurrence2Scalar0Left_coeff_251_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_252 :
    recurrence2Scalar0Left.coeff 252 =
      -((((2235 * 10 ^ 70 +
        5013111489292384816588772390118635904146368320348518640739433550270866) * 10 ^ 70 +
        9789953501939289623233606063028003798045834390376321087520826502935027) * 10 ^ 70 +
        4215698766616678584746432801533911729348071182439464548706738073768752) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 134 +
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
  rw [recurrence2Scalar0Left_coeff_252_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_253 :
    recurrence2Scalar0Left.coeff 253 =
      ((((1957 * 10 ^ 70 +
        4707689098844416364159422261593376016458785768213412563751884775941276) * 10 ^ 70 +
        9593482993378843817851300500125147240696817476453681342473424158687348) * 10 ^ 70 +
        2365659783285374709217176723270097556253112405952518951462547311781950) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 135 +
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
  rw [recurrence2Scalar0Left_coeff_253_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_254 :
    recurrence2Scalar0Left.coeff 254 =
      -((((1632 * 10 ^ 70 +
        7327214547659729423457591824067524031260883359827303188222391664166230) * 10 ^ 70 +
        9071846114794916654206449750991604015309029225473224224573547797032973) * 10 ^ 70 +
        5742408301915137123935452852921022820664777417164660016984069230513170) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 136 +
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
  rw [recurrence2Scalar0Left_coeff_254_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_255 :
    recurrence2Scalar0Left.coeff 255 =
      ((((1302 * 10 ^ 70 +
        6221107580814811306154132480549583024319676368613740566011711547730905) * 10 ^ 70 +
        9134798278427189975066262170662036288865586229185404423640386119072197) * 10 ^ 70 +
        5398450603464977819318486779041805780737978720291695990095706074817977) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 137 +
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
  rw [recurrence2Scalar0Left_coeff_255_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_256 :
    recurrence2Scalar0Left.coeff 256 =
      -((((996 * 10 ^ 70 +
        3669867699707944727616819915328535224449079556363559559940672402064171) * 10 ^ 70 +
        9775831075967996729001137409645283649899574425552645669871886870287338) * 10 ^ 70 +
        5576852383982616418436887204300658515569251867764901523615336845520662) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 138 +
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
  rw [recurrence2Scalar0Left_coeff_256_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_257 :
    recurrence2Scalar0Left.coeff 257 =
      ((((731 * 10 ^ 70 +
        4353295244741897716150426065741651721667291407203906027439523746583469) * 10 ^ 70 +
        6683287814248049488267432422726772712652214635715781791887454507812311) * 10 ^ 70 +
        4755673383426421723492393127616913376416375665626012216824018311945685) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 139 +
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
  rw [recurrence2Scalar0Left_coeff_257_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_258 :
    recurrence2Scalar0Left.coeff 258 =
      -((((515 * 10 ^ 70 +
        3255426890082522746422430095021359278030620326600615006230908305911908) * 10 ^ 70 +
        3477699281586768221835713244327761407438112820517062645452952287185604) * 10 ^ 70 +
        2539714106628701868872742850593379108221687487145535069057068751205586) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 140 +
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
  rw [recurrence2Scalar0Left_coeff_258_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_259 :
    recurrence2Scalar0Left.coeff 259 =
      ((((348 * 10 ^ 70 +
        0752519827901355206694124503564085902505860683457858318062167640838954) * 10 ^ 70 +
        6316083784567726967684845154940206156179891446761431161523024511552143) * 10 ^ 70 +
        7547994513205943108339460538679287377022044258995684408277126432586531) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 141 +
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
  rw [recurrence2Scalar0Left_coeff_259_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_260 :
    recurrence2Scalar0Left.coeff 260 =
      -((((224 * 10 ^ 70 +
        8837573986826452103017266734893939258866212154223405038157001740040327) * 10 ^ 70 +
        3754465410112505074025786804730685602570452186386530868685649774745438) * 10 ^ 70 +
        1412700325148950522695936458284276731309240234703625061526630510299440) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 142 +
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
  rw [recurrence2Scalar0Left_coeff_260_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_261 :
    recurrence2Scalar0Left.coeff 261 =
      ((((138 * 10 ^ 70 +
        4303759736970614633736238155255201547998466402798863632075947167486206) * 10 ^ 70 +
        5201619083232256814655400518951070602791688340374418918600291205326134) * 10 ^ 70 +
        1794502772864902461460660761483189027640251618729161041167841533724129) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 143 +
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
  rw [recurrence2Scalar0Left_coeff_261_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_262 :
    recurrence2Scalar0Left.coeff 262 =
      -((((80 * 10 ^ 70 +
        6653269756217027618234927843998519867558437332525914944011131290241021) * 10 ^ 70 +
        2558948665781063435013683354137873789540348044951565507844509133171966) * 10 ^ 70 +
        5067284436272958194375787607857755387950432906105174796080859642620341) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 144 +
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
  rw [recurrence2Scalar0Left_coeff_262_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_263 :
    recurrence2Scalar0Left.coeff 263 =
      ((((44 * 10 ^ 70 +
        0129453667092273991703075417049215824967731122093920842055007109604533) * 10 ^ 70 +
        4728753047074687853425813593474284490715635043386337867395985885251515) * 10 ^ 70 +
        4549158442908772759340035207019349731003674448047350590542260232825412) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 145 +
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
  rw [recurrence2Scalar0Left_coeff_263_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_264 :
    recurrence2Scalar0Left.coeff 264 =
      -((((22 * 10 ^ 70 +
        0405844279578019712444758346682514393924004767701043939545049041994494) * 10 ^ 70 +
        9411759246683680136445926963654021064306099513153614138355350518763277) * 10 ^ 70 +
        2363499605815203002251112473231333077528820564217531593417796562235942) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 146 +
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
  rw [recurrence2Scalar0Left_coeff_264_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_265 :
    recurrence2Scalar0Left.coeff 265 =
      ((((9 * 10 ^ 70 +
        7086748920823271512181310730484557059063090398771160681973136708390356) * 10 ^ 70 +
        1890484215169742066894709227438399469717535203415709251461468111259018) * 10 ^ 70 +
        3050826318416569664124441198078468134727110009873381486147536092643169) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 147 +
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
  rw [recurrence2Scalar0Left_coeff_265_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_266 :
    recurrence2Scalar0Left.coeff 266 =
      -((((3 * 10 ^ 70 +
        3365331324918413668747007049318807920415926515173409097224893059116025) * 10 ^ 70 +
        2309992821621255603739485456207655024364126701035442711178798972222783) * 10 ^ 70 +
        9911257388863293070211351816492971012453272264968160404522498876337858) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 148 +
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
  rw [recurrence2Scalar0Left_coeff_266_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_267 :
    recurrence2Scalar0Left.coeff 267 =
      (((4078525747702871299757396308236880890193106180016228060837012699275828 * 10 ^ 70 +
        8308720311700111545195410625280085335861911969364750533513719157320915) * 10 ^ 70 +
        6122199696920957386276340692273423459451292708398059316597212477630011) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 149 +
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
  rw [recurrence2Scalar0Left_coeff_267_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_268 :
    recurrence2Scalar0Left.coeff 268 =
      (((6870643032497612727564255685181634434775187414176560039324229959997435 * 10 ^ 70 +
        3276978819509970026537487608293759599055583270193993939827790387019587) * 10 ^ 70 +
        6302482302020979726043941585470874833306608842358645549332157083688125) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 150 +
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
  rw [recurrence2Scalar0Left_coeff_268_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_269 :
    recurrence2Scalar0Left.coeff 269 =
      -(((9071434387300656745117418366606945076005673748077717502580814251968499 * 10 ^ 70 +
        9211219022823938017677760884882113494027022666109948030776584762218712) * 10 ^ 70 +
        5686459396410622291863816320122816354589656612114953980331948009418181) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 151 +
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (270 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_270 :
    recurrence2Scalar0Left.coeff 270 =
      (((7784360680628956792169924123946087260681175156401155633211097415448784 * 10 ^ 70 +
        3142211232881263050693841487907502188069741711691435179274646634163620) * 10 ^ 70 +
        0552527458833888218460920781826062451690466713832205351493378591397923) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 152 +
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
    rw [show 23 = 21 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (271 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_271 :
    recurrence2Scalar0Left.coeff 271 =
      -(((5604976650371474375627053655083887878778960326329279277340425939702424 * 10 ^ 70 +
        4921346911441263993360895472193436205795875611133828169942311837419492) * 10 ^ 70 +
        0704670832987992109160405046059837999325447747145480698979851147221871) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 153 +
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
    rw [show 23 = 20 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (272 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_272 :
    recurrence2Scalar0Left.coeff 272 =
      (((3622553259906066889008402757606564104729791383624257067979578108411103 * 10 ^ 70 +
        7286869207113395311852228168551018814874238000165068505813500966781846) * 10 ^ 70 +
        3742366856801869467014907400913073869967214850926625454019653876059573) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 154 +
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
    rw [show 23 = 19 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (273 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_273 :
    recurrence2Scalar0Left.coeff 273 =
      -(((2159688178277758047327046418090966170767547699563185258786652187219467 * 10 ^ 70 +
        7242609280681263875819149867181811401017064082858742719866394225403631) * 10 ^ 70 +
        1496464607668881441328633355318569394648332165622544036053708665939875) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 155 +
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
    rw [show 23 = 18 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (274 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_274 :
    recurrence2Scalar0Left.coeff 274 =
      (((1203347489683287888870416616252323052209590409731755133913184785813785 * 10 ^ 70 +
        5793903537092278362750742129397280697163206371527452152592610112852436) * 10 ^ 70 +
        7393020998630876631200684652282589142872795324074460587440040563862106) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 156 +
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
    rw [show 23 = 17 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
