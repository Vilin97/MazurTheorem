/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (309 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_309 :
    recurrence2Scalar0Left.coeff 309 =
      -(((712962873099537560374187841228764282319280473690977 * 10 ^ 70 +
        8844435594556174377119947966475031016773457264354599616965564776345761) * 10 ^ 70 +
        3878244708157871164715832310740781631386036021628251059131907382503343) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 191 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 14 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (310 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_310 :
    recurrence2Scalar0Left.coeff 310 =
      -(((12264364436915593515187237120153698001495300200604 * 10 ^ 70 +
        2743533861390257399537049213284567280760775492337117375202076785018530) * 10 ^ 70 +
        9026657986236607194756109683053713376067593848029322600709847713270527) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 192 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 13 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (311 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_311 :
    recurrence2Scalar0Left.coeff 311 =
      (((26733877445043090053021017976408944130743120178293 * 10 ^ 70 +
        4100997798023990539952999158928308610507151661407259264101288766864363) * 10 ^ 70 +
        4657848271894697582576087627609768677274038072354397412718657038363097) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 193 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 12 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (312 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_312 :
    recurrence2Scalar0Left.coeff 312 =
      -(((8284550868544655167606285717090721499841659087872 * 10 ^ 70 +
        8553969551543811383594166751989606324898507024330137071154641697864304) * 10 ^ 70 +
        4521720802511470759656454347398224507254777927888718815236188329858526) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 194 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 11 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (313 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_313 :
    recurrence2Scalar0Left.coeff 313 =
      (((1847661331918508174561333732266335081642824243033 * 10 ^ 70 +
        3411232299387669555955080798968493084022330403273502369300864140471732) * 10 ^ 70 +
        7196925113096043949495976517629522302954577924991412161948948597834381) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 195 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 10 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (314 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_314 :
    recurrence2Scalar0Left.coeff 314 =
      -(((343175472794464526948799310473127807372768033169 * 10 ^ 70 +
        8536561665142901897258323792833130790607352747884312823942444193990836) * 10 ^ 70 +
        2088878704761916281836484094765725530916756804313926221134943669434418) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 196 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 9 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (315 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_315 :
    recurrence2Scalar0Left.coeff 315 =
      (((55379129825453295911318901353116781182489827066 * 10 ^ 70 +
        7737382595968321927352926688470191433237770111919880575765727674316044) * 10 ^ 70 +
        4300372748600282266911781495921864504471037688373206026185942658721875) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 197 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 8 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (316 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_316 :
    recurrence2Scalar0Left.coeff 316 =
      -(((7848291173427261641914610215848601839396637977 * 10 ^ 70 +
        6657213134710602827204356482840337282497564280355895242107197005353812) * 10 ^ 70 +
        9489133861135769802741738501928944995986508416939122327312632358651350) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 198 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 7 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (317 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_317 :
    recurrence2Scalar0Left.coeff 317 =
      (((967339076056192062211058122078539914301116190 * 10 ^ 70 +
        8105579500496733652365268416571111167319830131054130131763124993298588) * 10 ^ 70 +
        8890700381039839384807475711664219132209697957940384258436264394975133) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 199 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 6 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (318 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_318 :
    recurrence2Scalar0Left.coeff 318 =
      -(((99556399345891246265946547571755902815731541 * 10 ^ 70 +
        0463820928499923380432893812899084716164023371785671644790090478987543) * 10 ^ 70 +
        5444407229391590149292198701044284688555873468864665753224027394435623) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 200 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 5 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (319 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_319 :
    recurrence2Scalar0Left.coeff 319 =
      (((7443756064830287147589435292702190514737787 * 10 ^ 70 +
        4394201308646465426984484099909496562849582666951522786501526625128811) * 10 ^ 70 +
        2169328829767090274396548866729798221869534125936263849731266046383161) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 201 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 4 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (320 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_320 :
    recurrence2Scalar0Left.coeff 320 =
      -(((107574314259787404500494314479812290076573 * 10 ^ 70 +
        3001304442184782888327447980237589917983853435940566654567594266958601) * 10 ^ 70 +
        6227117309777665479919706882606208063015001407030354830474632630678632) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 202 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 3 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (321 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_321 :
    recurrence2Scalar0Left.coeff 321 =
      -(((94603000283693962999864298631117375336937 * 10 ^ 70 +
        9454768483480598774936618943310160961736550709081779549042088112339919) * 10 ^ 70 +
        9429496421633346259938502293813117126480725130935985940007893919498699) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 203 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 2 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (322 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_322 :
    recurrence2Scalar0Left.coeff 322 =
      (((23126533298365890953945634367788197400776 * 10 ^ 70 +
        7445132615917295443803174991084436146216592866757280749199427365957789) * 10 ^ 70 +
        2604970998308944474207423949269803473521351242127934245215308930615927) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 204 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 1 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (323 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_323 :
    recurrence2Scalar0Left.coeff 323 =
      -(((3717451970750719365740929602494948098318 * 10 ^ 70 +
        6758118429903228123122238781622899638157199851159284578588670054574380) * 10 ^ 70 +
        4153082109016000596114459757357276880976677420201401918119551276383960) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 205 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (324 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_324 :
    recurrence2Scalar0Left.coeff 324 =
      (((474060458432510695705727790452460784489 * 10 ^ 70 +
        6155295560804926434504721916807468441373796857746052545933325578286793) * 10 ^ 70 +
        6609330451247941504628306834339755244743564364661327974211062427043778) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 206 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 31 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (325 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_325 :
    recurrence2Scalar0Left.coeff 325 =
      -(((49360163516387917409765693543920757769 * 10 ^ 70 +
        2104021297921792757407451521636766213115234226029001072003281473315959) * 10 ^ 70 +
        7189518213979376708822454150224703040994915825013694228152213663752883) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 207 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 30 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (326 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_326 :
    recurrence2Scalar0Left.coeff 326 =
      (((4031095699685929672625689051365031035 * 10 ^ 70 +
        4824021659353191184655637806680214463644384721421253585730357502020532) * 10 ^ 70 +
        1691180267720746117866822102808071189329062760343341151211698284013854) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 208 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 29 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (327 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_327 :
    recurrence2Scalar0Left.coeff 327 =
      -(((212574222187937997110349061246290100 * 10 ^ 70 +
        3501441487244692224632336449808558032945578950293488978242022951402526) * 10 ^ 70 +
        0284803163143519144381546828018071511068755358798978356637862516140147) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 209 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 28 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (328 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_328 :
    recurrence2Scalar0Left.coeff 328 =
      -(((2436934416261168005066180035820634 * 10 ^ 70 +
        2630656957700349934270667193710056115478107002674296362399644364983244) * 10 ^ 70 +
        0573694522727805195878450148935724382762932668052598611460951328064221) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 210 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 27 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (329 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_329 :
    recurrence2Scalar0Left.coeff 329 =
      (((2276908397891162044679189310621014 * 10 ^ 70 +
        6126982286713715086390827577259747607972033425252759194016393514018837) * 10 ^ 70 +
        6860994693743217238154894172634298169503903181436789788736598608808257) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 211 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (330 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_330 :
    recurrence2Scalar0Left.coeff 330 =
      -(((328000199020455480878410794994615 * 10 ^ 70 +
        3692697383158801701402553091457179087564818913499410786153256336582757) * 10 ^ 70 +
        8079795598906857969362026880416043431137248363520187503777367091600876) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 212 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 25 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (331 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_331 :
    recurrence2Scalar0Left.coeff 331 =
      (((30289266453481083047987681683454 * 10 ^ 70 +
        5192420908923345793156829412041193299613796573109532801435206422163705) * 10 ^ 70 +
        5372187810326948069233029169685778983229762777549408266159037306220983) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 213 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 24 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (332 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_332 :
    recurrence2Scalar0Left.coeff 332 =
      -(((1877565466017358150315406870413 * 10 ^ 70 +
        7273303939825340610418376311756744358292752115165034450585943070175148) * 10 ^ 70 +
        8257061776693460194594414820571144426548417441928390198756959519416086) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 214 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (333 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_333 :
    recurrence2Scalar0Left.coeff 333 =
      (((51938218172851430573973218944 * 10 ^ 70 +
        3734634440296300047667437339967947488398274928824318803216079386252584) * 10 ^ 70 +
        5453058312934622657510530499717464378816205687491223394394429257144562) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 215 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 22 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (334 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_334 :
    recurrence2Scalar0Left.coeff 334 =
      (((4327438710950299821951868937 * 10 ^ 70 +
        6275307830457282291960176288274549536381271987301728466326310201585977) * 10 ^ 70 +
        3760307617089374523917652358800626377789343760162407225801574246992400) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 216 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 21 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (335 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_335 :
    recurrence2Scalar0Left.coeff 335 =
      -(((750476104334396943556657867 * 10 ^ 70 +
        0731026664822022661757592555010043023592035214684071840974833056698808) * 10 ^ 70 +
        2401350957728846956928751263665522803281105561229929656231076677245003) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 217 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 20 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (336 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_336 :
    recurrence2Scalar0Left.coeff 336 =
      (((59347853580521987605126635 * 10 ^ 70 +
        9519826663423166588735270623665825457166513954421685688285332307700541) * 10 ^ 70 +
        4895429556879968398805332066564666493610408152135351864165148495156127) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 218 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (337 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_337 :
    recurrence2Scalar0Left.coeff 337 =
      -(((2796558143084206163998519 * 10 ^ 70 +
        2622771000069686896847216048190250143206818177069275064117842848333427) * 10 ^ 70 +
        7631400923800996633581841992312825764285146993775564580086410533846337) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 219 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 18 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (338 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_338 :
    recurrence2Scalar0Left.coeff 338 =
      (((44178320123045435906191 * 10 ^ 70 +
        6832291671091440564004707608711961340793807484898927781596068750480387) * 10 ^ 70 +
        3637859132658620029497639542782192505526812275228568339421168931166087) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 220 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 17 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (339 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_339 :
    recurrence2Scalar0Left.coeff 339 =
      (((4907344720404843491479 * 10 ^ 70 +
        2743351997742545161632276194934237692924151732699024294891025351691799) * 10 ^ 70 +
        6139367732896310915435009285816852099394904218441565639006227746178427) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 221 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (340 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_340 :
    recurrence2Scalar0Left.coeff 340 =
      -(((494219462829885113804 * 10 ^ 70 +
        7429452543483805472558517225927060119489932739701429870198869003891746) * 10 ^ 70 +
        2534906102650049350828980787342221750105745227377991754775398638904305) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 222 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (341 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_341 :
    recurrence2Scalar0Left.coeff 341 =
      (((23516903397011475492 * 10 ^ 70 +
        9814022138006174367482648981675391700452341334182933987821210760582501) * 10 ^ 70 +
        8578556763017035651396329290299390289381779860404483932413620857653341) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 223 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 14 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (342 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_342 :
    recurrence2Scalar0Left.coeff 342 =
      -(((550568247034722056 * 10 ^ 70 +
        2684324187440794783439940547229206780731207105480609615034309092966226) * 10 ^ 70 +
        1701707854510239589028277453647529759293905323336564497709692377505697) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 224 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 13 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (343 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_343 :
    recurrence2Scalar0Left.coeff 343 =
      -(((5732490478757103 * 10 ^ 70 +
        8633932084050728484170110615688300161123979792218303911581298124673250) * 10 ^ 70 +
        7925498374039214318693934792690873538806289250127551625490336932771063) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 225 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (344 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_344 :
    recurrence2Scalar0Left.coeff 344 =
      (((991165877872832 * 10 ^ 70 +
        0821429387209375484822415480441219272011214143188471053806466308295721) * 10 ^ 70 +
        0718322112443478334898250270964540816191941883826103683253968232599781) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 226 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 11 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (345 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_345 :
    recurrence2Scalar0Left.coeff 345 =
      -(((37460510214738 * 10 ^ 70 +
        1914458488732155291162844510124718789850432698854440119330637323173312) * 10 ^ 70 +
        5782222826185269523623708409991914956338366303387753575295715294508986) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 227 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 10 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (346 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_346 :
    recurrence2Scalar0Left.coeff 346 =
      (((602726364144 * 10 ^ 70 +
        7720596109527255269028869902579108772043132088795189005292200594474130) * 10 ^ 70 +
        9254159739036816547418072272234188452875779364151862871220027863386091) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 228 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 9 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (347 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_347 :
    recurrence2Scalar0Left.coeff 347 =
      (((4818180112 * 10 ^ 70 +
        7552807916779010608223894719688312284532503553551434503618973124024772) * 10 ^ 70 +
        3421247249922822632825636787795228223625085900719836507464713770389989) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 229 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 8 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (348 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_348 :
    recurrence2Scalar0Left.coeff 348 =
      -(((438609173 * 10 ^ 70 +
        1917369725048479067322702343016266965065566800160853603760558462847693) * 10 ^ 70 +
        4553344931418517145193815478687348128752591973100435277925219237175270) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 230 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 7 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (349 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_349 :
    recurrence2Scalar0Left.coeff 349 =
      (((8172799 * 10 ^ 70 +
        4966861413061417102450245583892166020421242790048688349769234698879584) * 10 ^ 70 +
        5691736476195777064115557423715968669701550468363181010122560231802032) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 231 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 6 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (350 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_350 :
    recurrence2Scalar0Left.coeff 350 =
      -(((23267 * 10 ^ 70 +
        4610725156070776877087913982061843420586398264151109810030638503645306) * 10 ^ 70 +
        2102758995459976005525701568659903724251604636096050056450884891570837) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 232 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 5 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (351 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_351 :
    recurrence2Scalar0Left.coeff 351 =
      -(((1474 * 10 ^ 70 +
        3436109901348210540877611100133878851643481777005778413100108684952535) * 10 ^ 70 +
        2209940461431872960391627647023338577078118232920920056019500918996762) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 233 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 4 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (352 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_352 :
    recurrence2Scalar0Left.coeff 352 =
      (((21 * 10 ^ 70 +
        2320141916145840777933148322479745870666262126663741602044120865134071) * 10 ^ 70 +
        2756837302400232102474323094393494043750974296301523884839639353433186) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 234 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 3 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (353 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_353 :
    recurrence2Scalar0Left.coeff 353 =
      -((31283622737869721844428422430697049791768818395365787944783458900813 * 10 ^ 70 +
        1826977566619105078481075960256247184138828739085993962592914877077956) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 235 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 2 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (354 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_354 :
    recurrence2Scalar0Left.coeff 354 =
      -((20712939699920919781161904580841409585186214742908383244391213202834 * 10 ^ 70 +
        4349277687707931919276718895802870175982910560794187991608672431490785) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 236 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 1 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (355 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_355 :
    recurrence2Scalar0Left.coeff 355 =
      ((110119853462536740682318063962785199840063861765040551608059583076 * 10 ^ 70 +
        8911580530512556496186425808727783278895720009010472069513919959690098) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 237 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (356 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_356 :
    recurrence2Scalar0Left.coeff 356 =
      ((807866841954856872055661297878613716565879991085462955111547901 * 10 ^ 70 +
        6023383611677053093222952290931366223347628057077416254885046917625331) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 238 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 31 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (357 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_357 :
    recurrence2Scalar0Left.coeff 357 =
      -((7641448080099108419549230501588343722359547364155662770373031 * 10 ^ 70 +
        8950547462165429426748128321467116883397297119634000701275192155569383) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 239 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 30 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (358 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_358 :
    recurrence2Scalar0Left.coeff 358 =
      -((11478910450598998111811123740405834717185190256699555068733 * 10 ^ 70 +
        9406996855655098609148495801152657332884586295451465272688789649783802) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 240 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 29 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (359 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_359 :
    recurrence2Scalar0Left.coeff 359 =
      ((243120966036029580436782480625446491485763241173482593616 * 10 ^ 70 +
        0974544207310745696570709975777179663530498924492866533263150767641625) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 241 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 28 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (360 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_360 :
    recurrence2Scalar0Left.coeff 360 =
      -((138613397412489368589896817523413887254907015326079947 * 10 ^ 70 +
        3278113333142488945808007631593838422492583509681729720255575186435681) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 242 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 27 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (361 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_361 :
    recurrence2Scalar0Left.coeff 361 =
      -((4127276135491631994824318902095658493529341322923568 * 10 ^ 70 +
        4026692610149340294734435618819408165072105914044194070983723501549825) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 243 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (362 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_362 :
    recurrence2Scalar0Left.coeff 362 =
      ((7517651384548606338218616520240456823526742125129 * 10 ^ 70 +
        2729362270244790677934882111570574297083646447425599479788383085771604) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 244 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 25 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (363 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_363 :
    recurrence2Scalar0Left.coeff 363 =
      ((35692804540470748533763939623158935657105382080 * 10 ^ 70 +
        6601961465084447637946952634488573682500057632789685671616609138689168) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 245 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 24 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (364 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_364 :
    recurrence2Scalar0Left.coeff 364 =
      -((110673247875388126254444989626750632948448759 * 10 ^ 70 +
        6533233184045514480554877577709476519744041029607514264675089310516604) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 246 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 23 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (365 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_365 :
    recurrence2Scalar0Left.coeff 365 =
      -((99476313832032804741351098359958755125651 * 10 ^ 70 +
        9046536496211635913688463598185621647716888278367326277903318813010717) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 247 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 22 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (366 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_366 :
    recurrence2Scalar0Left.coeff 366 =
      ((706970114857671076175737342246765459703 * 10 ^ 70 +
        3623799852255835175440437290002835084505296085700537874029173956619767) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 248 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 21 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (367 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_367 :
    recurrence2Scalar0Left.coeff 367 =
      -((520170693036158563920977141204687180 * 10 ^ 70 +
        2556349387547009422925617259160668948627071414394403057371076976017369) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 249 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 20 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (368 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_368 :
    recurrence2Scalar0Left.coeff 368 =
      -((1424947581553036619557858093853271 * 10 ^ 70 +
        1501623529243635306028101762068622348294819716961703590663843333759496) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 250 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 19 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (369 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_369 :
    recurrence2Scalar0Left.coeff 369 =
      ((2939394726691927269541260224317 * 10 ^ 70 +
        6368771181641950845109764546405520789387130265460418427297109691441104) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 251 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 18 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (370 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_370 :
    recurrence2Scalar0Left.coeff 370 =
      -((1613487975609704182780794678 * 10 ^ 70 +
        0077770061524046726943080484031467854678257680800763140434873415704311) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 252 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 17 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (371 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_371 :
    recurrence2Scalar0Left.coeff 371 =
      -((631026964657470926901793 * 10 ^ 70 +
        7211935126102909438307112977834321918308233337979550144027038865918835) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 253 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (372 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_372 :
    recurrence2Scalar0Left.coeff 372 =
      ((1118107532394298380736 * 10 ^ 70 +
        0962160936849959688682661646046476558981865364658835613652418092859138) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 254 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 15 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (373 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_373 :
    recurrence2Scalar0Left.coeff 373 =
      -((479171976249628930 * 10 ^ 70 +
        8060246407546055881077186596629329305094786395931786149297290244422616) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 255 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 14 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (374 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_374 :
    recurrence2Scalar0Left.coeff 374 =
      ((74066801879720 * 10 ^ 70 +
        5393913089967303228004112804203056973705485873499681212000017186691903) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 256 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 13 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (375 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_375 :
    recurrence2Scalar0Left.coeff 375 =
      ((970864945 * 10 ^ 70 +
        3009424948101878061726687189685969866900168829174656100113647963500142) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 257 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 12 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (376 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_376 :
    recurrence2Scalar0Left.coeff 376 =
      -((1314719 * 10 ^ 70 +
        1616093944301141621699451930411492863398999175263717420162632617754145) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 258 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 11 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (377 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_377 :
    recurrence2Scalar0Left.coeff 377 =
      ((109 * 10 ^ 70 +
        5153536682224712461555173334163008397292481860953190654714748253647229) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 259 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 10 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (378 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_378 :
    recurrence2Scalar0Left.coeff 378 =
      (-30702924267016725490650486023379308864570185634675172082413865355289 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 260 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 9 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (379 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_379 :
    recurrence2Scalar0Left.coeff 379 =
      (193637924496439561704066822450592910243002054890567563833694657 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 261 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 8 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (380 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_380 :
    recurrence2Scalar0Left.coeff 380 =
      (1331078207138453835966744528248787424416136493715184769404 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 381 = 262 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 7 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (381 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_381 :
    recurrence2Scalar0Left.coeff 381 =
      (-13708128010898880438623614707092479808719596666307193 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 382 = 263 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 6 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (382 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_382 :
    recurrence2Scalar0Left.coeff 382 =
      (18751414389841545523553731614982178201543911010 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 383 = 264 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 5 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (383 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_383 :
    recurrence2Scalar0Left.coeff 383 =
      (-6968666422007133725421629603848396585859 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 384 = 265 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 4 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (384 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_384 :
    recurrence2Scalar0Left.coeff 384 =
      (-11169886686358548984931405851122 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 385 = 266 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 3 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (385 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_385 :
    recurrence2Scalar0Left.coeff 385 =
      (1109519187941616171668366 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 386 = 267 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 2 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar0Left_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (386 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_386 :
    recurrence2Scalar0Left.coeff 386 =
      (-4877303983489137 : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 387 = 268 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 1 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
