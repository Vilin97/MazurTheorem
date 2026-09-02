/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5LeadingSquare_coeff_0
  recurrence5LeadingSquare_coeff_1
  recurrence5LeadingSquare_coeff_2
  recurrence5LeadingSquare_coeff_3
  recurrence5LeadingSquare_coeff_4
  recurrence5LeadingSquare_coeff_5
  recurrence5LeadingSquare_coeff_6
  recurrence5LeadingSquare_coeff_7
  recurrence5LeadingSquare_coeff_8
  recurrence5LeadingSquare_coeff_9
  recurrence5LeadingSquare_coeff_10
  recurrence5LeadingSquare_coeff_11
  recurrence5LeadingSquare_coeff_12
  recurrence5LeadingSquare_coeff_13
  recurrence5LeadingSquare_coeff_14
  recurrence5LeadingSquare_coeff_15
  recurrence5LeadingSquare_coeff_16
  recurrence5LeadingSquare_coeff_17
  recurrence5LeadingSquare_coeff_18
  recurrence5LeadingSquare_coeff_19
  recurrence5LeadingSquare_coeff_20
  recurrence5LeadingSquare_coeff_21
  recurrence5LeadingSquare_coeff_22
  recurrence5LeadingSquare_coeff_23
  recurrence5LeadingSquare_coeff_24
  recurrence5LeadingSquare_coeff_25
  recurrence5LeadingSquare_coeff_26
  recurrence5LeadingSquare_coeff_27
  recurrence5LeadingSquare_coeff_28
  recurrence5LeadingSquare_coeff_29
  recurrence5LeadingSquare_coeff_30
  recurrence5LeadingSquare_coeff_31
  recurrence5LeadingSquare_coeff_32
  recurrence5LeadingSquare_coeff_33
  recurrence5LeadingSquare_coeff_34
  recurrence5LeadingSquare_coeff_35
  recurrence5LeadingSquare_coeff_36
  recurrence5LeadingSquare_coeff_37
  recurrence5LeadingSquare_coeff_38
  recurrence5LeadingSquare_coeff_39
  recurrence5LeadingSquare_coeff_40
  recurrence5LeadingSquare_coeff_41
  recurrence5LeadingSquare_coeff_42
  recurrence5LeadingSquare_coeff_43
  recurrence5LeadingSquare_coeff_44
  recurrence5LeadingSquare_coeff_45
  recurrence5LeadingSquare_coeff_46
  recurrence5LeadingSquare_coeff_47
  recurrence5LeadingSquare_coeff_48
  recurrence5LeadingSquare_coeff_49
  recurrence5LeadingSquare_coeff_50
  recurrence5LeadingSquare_coeff_51
  recurrence5LeadingSquare_coeff_52
  recurrence5LeadingSquare_coeff_53
  recurrence5LeadingSquare_coeff_54
  recurrence5LeadingSquare_coeff_55
  recurrence5LeadingSquare_coeff_56
  recurrence5LeadingSquare_coeff_57
  recurrence5LeadingSquare_coeff_58
  recurrence5LeadingSquare_coeff_59
  recurrence5LeadingSquare_coeff_60
  recurrence5LeadingSquare_coeff_61
  recurrence5LeadingSquare_coeff_62
  recurrence5LeadingSquare_coeff_63

attribute [local simp]
  recurrence5LeadingSquare_coeff_64
  recurrence5LeadingSquare_coeff_65
  recurrence5LeadingSquare_coeff_66
  recurrence5LeadingSquare_coeff_67
  recurrence5LeadingSquare_coeff_68
  recurrence5LeadingSquare_coeff_69
  recurrence5LeadingSquare_coeff_70
  recurrence5LeadingSquare_coeff_71
  recurrence5LeadingSquare_coeff_72
  recurrence5LeadingSquare_coeff_73
  recurrence5LeadingSquare_coeff_74
  recurrence5LeadingSquare_coeff_75
  recurrence5LeadingSquare_coeff_76
  recurrence5LeadingSquare_coeff_77
  recurrence5LeadingSquare_coeff_78
  recurrence5LeadingSquare_coeff_79
  recurrence5LeadingSquare_coeff_80
  recurrence5LeadingSquare_coeff_81
  recurrence5LeadingSquare_coeff_82
  recurrence5LeadingSquare_coeff_83
  recurrence5LeadingSquare_coeff_84
  recurrence5LeadingSquare_coeff_85
  recurrence5LeadingSquare_coeff_86
  recurrence5LeadingSquare_coeff_87
  recurrence5LeadingSquare_coeff_88
  recurrence5LeadingSquare_coeff_89
  recurrence5LeadingSquare_coeff_90
  recurrence5LeadingSquare_coeff_91
  recurrence5LeadingSquare_coeff_92
  recurrence5LeadingSquare_coeff_93
  recurrence5LeadingSquare_coeff_94
  recurrence5LeadingSquare_coeff_95
  recurrence5LeadingSquare_coeff_96
  recurrence5LeadingSquare_coeff_97
  recurrence5LeadingSquare_coeff_98
  recurrence5LeadingSquare_coeff_99
  recurrence5LeadingSquare_coeff_100
  recurrence5LeadingSquare_coeff_101
  recurrence5LeadingSquare_coeff_102
  recurrence5LeadingSquare_coeff_103
  recurrence5LeadingSquare_coeff_104
  recurrence5LeadingSquare_coeff_105
  recurrence5LeadingSquare_coeff_106
  recurrence5LeadingSquare_coeff_107
  recurrence5LeadingSquare_coeff_108
  recurrence5LeadingSquare_coeff_109
  recurrence5LeadingSquare_coeff_110
  recurrence5LeadingSquare_coeff_111
  recurrence5LeadingSquare_coeff_112
  recurrence5LeadingSquare_coeff_113
  recurrence5LeadingSquare_coeff_114
  recurrence5LeadingSquare_coeff_115
  recurrence5LeadingSquare_coeff_116
  recurrence5LeadingSquare_coeff_117
  recurrence5LeadingSquare_coeff_118
  recurrence5LeadingSquare_coeff_119
  recurrence5LeadingSquare_coeff_120
  recurrence5LeadingSquare_coeff_121
  recurrence5LeadingSquare_coeff_122
  recurrence5LeadingSquare_coeff_123
  recurrence5LeadingSquare_coeff_124
  recurrence5LeadingSquare_coeff_125
  recurrence5LeadingSquare_coeff_126
  recurrence5LeadingSquare_coeff_127

attribute [local simp]
  recurrence5LeadingSquare_coeff_128
  recurrence5LeadingSquare_coeff_129
  recurrence5LeadingSquare_coeff_130
  recurrence5LeadingSquare_coeff_131
  recurrence5LeadingSquare_coeff_132
  recurrence5LeadingSquare_coeff_133
  recurrence5LeadingSquare_coeff_134
  recurrence5LeadingSquare_coeff_135
  recurrence5LeadingSquare_coeff_136
  recurrence5LeadingSquare_coeff_137
  recurrence5LeadingSquare_coeff_138
  recurrence5LeadingSquare_coeff_139
  recurrence5LeadingSquare_coeff_140
  recurrence5LeadingSquare_coeff_141
  recurrence5LeadingSquare_coeff_142
  recurrence5LeadingSquare_coeff_143
  recurrence5LeadingSquare_coeff_144
  recurrence5LeadingSquare_coeff_145
  recurrence5LeadingSquare_coeff_146
  recurrence5LeadingSquare_coeff_147
  recurrence5LeadingSquare_coeff_148
  recurrence5LeadingSquare_coeff_149
  recurrence5LeadingSquare_coeff_150
  recurrence5LeadingSquare_coeff_151
  recurrence5LeadingSquare_coeff_152
  recurrence5LeadingSquare_coeff_153
  recurrence5LeadingSquare_coeff_154
  recurrence5LeadingSquare_coeff_155
  recurrence5LeadingSquare_coeff_156
  recurrence5LeadingSquare_coeff_157
  recurrence5LeadingSquare_coeff_158
  recurrence5LeadingSquare_coeff_159
  recurrence5LeadingSquare_coeff_160
  recurrence5LeadingSquare_coeff_161
  recurrence5LeadingSquare_coeff_162
  recurrence5LeadingSquare_coeff_163
  recurrence5LeadingSquare_coeff_164
  recurrence5LeadingSquare_coeff_165
  recurrence5LeadingSquare_coeff_166
  recurrence5LeadingSquare_coeff_167
  recurrence5LeadingSquare_coeff_168
  recurrence5LeadingSquare_coeff_169
  recurrence5LeadingSquare_coeff_170
  recurrence5LeadingSquare_coeff_171
  recurrence5LeadingSquare_coeff_172
  recurrence5LeadingSquare_coeff_173
  recurrence5LeadingSquare_coeff_174
  recurrence5LeadingSquare_coeff_175
  recurrence5LeadingSquare_coeff_176
  recurrence5LeadingSquare_coeff_177
  recurrence5LeadingSquare_coeff_178
  recurrence5LeadingSquare_coeff_179
  recurrence5LeadingSquare_coeff_180
  recurrence5LeadingSquare_coeff_181
  recurrence5LeadingSquare_coeff_182
  recurrence5LeadingSquare_coeff_183
  recurrence5LeadingSquare_coeff_184
  recurrence5LeadingSquare_coeff_185
  recurrence5LeadingSquare_coeff_186
  recurrence5LeadingSquare_coeff_187
  recurrence5LeadingSquare_coeff_188
  recurrence5LeadingSquare_coeff_189
  recurrence5LeadingSquare_coeff_190
  recurrence5LeadingSquare_coeff_191

attribute [local simp]
  recurrence5LeadingSquare_coeff_192
  recurrence5LeadingSquare_coeff_193
  recurrence5LeadingSquare_coeff_194
  recurrence5LeadingSquare_coeff_195
  recurrence5LeadingSquare_coeff_196
  recurrence5LeadingSquare_coeff_197
  recurrence5LeadingSquare_coeff_198
  recurrence5LeadingSquare_coeff_199
  recurrence5LeadingSquare_coeff_200
  recurrence5LeadingSquare_coeff_201
  recurrence5LeadingSquare_coeff_202
  recurrence5LeadingSquare_coeff_203
  recurrence5LeadingSquare_coeff_204
  recurrence5LeadingSquare_coeff_205
  recurrence5LeadingSquare_coeff_206
  recurrence5LeadingSquare_coeff_207
  recurrence5LeadingSquare_coeff_208
  recurrence5LeadingSquare_coeff_209
  recurrence5LeadingSquare_coeff_210
  recurrence5LeadingSquare_coeff_211
  recurrence5LeadingSquare_coeff_212
  recurrence5LeadingSquare_coeff_213
  recurrence5LeadingSquare_coeff_214
  recurrence5LeadingSquare_coeff_215
  recurrence5LeadingSquare_coeff_216
  recurrence5LeadingSquare_coeff_217
  recurrence5LeadingSquare_coeff_218
  recurrence5LeadingSquare_coeff_219
  recurrence5LeadingSquare_coeff_220
  recurrence5LeadingSquare_coeff_221
  recurrence5LeadingSquare_coeff_222
  recurrence5LeadingSquare_coeff_223
  recurrence5LeadingSquare_coeff_224
  recurrence5LeadingSquare_coeff_225
  recurrence5LeadingSquare_coeff_226
  recurrence5LeadingSquare_coeff_227
  recurrence5LeadingSquare_coeff_228
  recurrence5LeadingSquare_coeff_229
  recurrence5LeadingSquare_coeff_230
  recurrence5LeadingSquare_coeff_231
  recurrence5LeadingSquare_coeff_232
  recurrence5LeadingSquare_coeff_233
  recurrence5LeadingSquare_coeff_234
  recurrence5LeadingSquare_coeff_235
  recurrence5LeadingSquare_coeff_236
  recurrence5LeadingSquare_coeff_237
  recurrence5LeadingSquare_coeff_238
  recurrence5LeadingSquare_coeff_239
  recurrence5LeadingSquare_coeff_240
  recurrence5LeadingSquare_coeff_241
  recurrence5LeadingSquare_coeff_242
  recurrence5LeadingSquare_coeff_243
  recurrence5LeadingSquare_coeff_244
  recurrence5LeadingSquare_coeff_245
  recurrence5LeadingSquare_coeff_246
  recurrence5LeadingSquare_coeff_247
  recurrence5LeadingSquare_coeff_248
  recurrence5LeadingSquare_coeff_249
  recurrence5LeadingSquare_coeff_250
  recurrence5LeadingSquare_coeff_251
  recurrence5LeadingSquare_coeff_252
  recurrence5LeadingSquare_coeff_253
  recurrence5LeadingSquare_coeff_254
  recurrence5LeadingSquare_coeff_255

attribute [local simp]
  recurrence5LeadingSquare_coeff_256
  recurrence5LeadingSquare_coeff_257
  recurrence5LeadingSquare_coeff_258
  recurrence5LeadingSquare_coeff_259
  recurrence5LeadingSquare_coeff_260
  recurrence5LeadingSquare_coeff_261
  recurrence5LeadingSquare_coeff_262
  recurrence5LeadingSquare_coeff_263
  recurrence5LeadingSquare_coeff_264
  recurrence5LeadingSquare_coeff_265
  recurrence5LeadingSquare_coeff_266
  recurrence5LeadingSquare_coeff_267
  recurrence5LeadingSquare_coeff_268
  recurrence5LeadingSquare_coeff_269
  recurrence5LeadingSquare_coeff_270
  recurrence5LeadingSquare_coeff_271
  recurrence5LeadingSquare_coeff_272
  recurrence5LeadingSquare_coeff_273
  recurrence5LeadingSquare_coeff_274
  recurrence5LeadingSquare_coeff_275
  recurrence5LeadingSquare_coeff_276
  recurrence5LeadingSquare_coeff_277
  recurrence5LeadingSquare_coeff_278
  recurrence5LeadingSquare_coeff_279
  recurrence5LeadingSquare_coeff_280
  recurrence5LeadingSquare_coeff_281
  recurrence5LeadingSquare_coeff_282
  recurrence5LeadingSquare_coeff_283
  recurrence5LeadingSquare_coeff_284
  recurrence5LeadingSquare_coeff_285
  recurrence5LeadingSquare_coeff_286
  recurrence5LeadingSquare_coeff_287
  recurrence5LeadingSquare_coeff_288
  recurrence5LeadingSquare_coeff_289
  recurrence5LeadingSquare_coeff_290
  recurrence5A0_coeff_0
  recurrence5A0_coeff_1
  recurrence5A0_coeff_2
  recurrence5A0_coeff_3
  recurrence5A0_coeff_4
  recurrence5A0_coeff_5
  recurrence5A0_coeff_6
  recurrence5A0_coeff_7
  recurrence5A0_coeff_8
  recurrence5A0_coeff_9
  recurrence5A0_coeff_10
  recurrence5A0_coeff_11
  recurrence5A0_coeff_12
  recurrence5A0_coeff_13
  recurrence5A0_coeff_14
  recurrence5A0_coeff_15
  recurrence5A0_coeff_16
  recurrence5A0_coeff_17
  recurrence5A0_coeff_18
  recurrence5A0_coeff_19
  recurrence5A0_coeff_20
  recurrence5A0_coeff_21
  recurrence5A0_coeff_22
  recurrence5A0_coeff_23
  recurrence5A0_coeff_24
  recurrence5A0_coeff_25
  recurrence5A0_coeff_26
  recurrence5A0_coeff_27
  recurrence5A0_coeff_28

attribute [local simp]
  recurrence5A0_coeff_29
  recurrence5A0_coeff_30
  recurrence5A0_coeff_31
  recurrence5A0_coeff_32
  recurrence5A0_coeff_33
  recurrence5A0_coeff_34
  recurrence5A0_coeff_35
  recurrence5A0_coeff_36
  recurrence5A0_coeff_37
  recurrence5A0_coeff_38
  recurrence5A0_coeff_39
  recurrence5A0_coeff_40
  recurrence5A0_coeff_41
  recurrence5A0_coeff_42
  recurrence5A0_coeff_43
  recurrence5A0_coeff_44
  recurrence5A0_coeff_45
  recurrence5A0_coeff_46
  recurrence5A0_coeff_47
  recurrence5A0_coeff_48
  recurrence5A0_coeff_49
  recurrence5A0_coeff_50
  recurrence5A0_coeff_51
  recurrence5A0_coeff_52
  recurrence5A0_coeff_53
  recurrence5A0_coeff_54
  recurrence5A0_coeff_55
  recurrence5A0_coeff_56
  recurrence5A0_coeff_57
  recurrence5A0_coeff_58
  recurrence5A0_coeff_59
  recurrence5A0_coeff_60
  recurrence5A0_coeff_61
  recurrence5A0_coeff_62
  recurrence5A0_coeff_63
  recurrence5A0_coeff_64
  recurrence5A0_coeff_65
  recurrence5A0_coeff_66
  recurrence5A0_coeff_67
  recurrence5A0_coeff_68
  recurrence5A0_coeff_69
  recurrence5A0_coeff_70
  recurrence5A0_coeff_71
  recurrence5A0_coeff_72
  recurrence5A0_coeff_73
  recurrence5A0_coeff_74
  recurrence5A0_coeff_75
  recurrence5A0_coeff_76
  recurrence5A0_coeff_77
  recurrence5A0_coeff_78
  recurrence5A0_coeff_79
  recurrence5A0_coeff_80
  recurrence5A0_coeff_81
  recurrence5A0_coeff_82
  recurrence5A0_coeff_83
  recurrence5A0_coeff_84
  recurrence5A0_coeff_85
  recurrence5A0_coeff_86
  recurrence5A0_coeff_87
  recurrence5A0_coeff_88
  recurrence5A0_coeff_89
  recurrence5A0_coeff_90
  recurrence5A0_coeff_91
  recurrence5A0_coeff_92

attribute [local simp]
  recurrence5A0_coeff_93
  recurrence5A0_coeff_94
  recurrence5A0_coeff_95
  recurrence5A0_coeff_96
  recurrence5A0_coeff_97
  recurrence5A0_coeff_98
  recurrence5A0_coeff_99
  recurrence5A0_coeff_100
  recurrence5A0_coeff_101
  recurrence5A0_coeff_102
  recurrence5A0_coeff_103
  recurrence5A0_coeff_104
  recurrence5A0_coeff_105
  recurrence5A0_coeff_106
  recurrence5A0_coeff_107
  recurrence5A0_coeff_108
  recurrence5A0_coeff_109
  recurrence5A0_coeff_110
  recurrence5A0_coeff_111
  recurrence5A0_coeff_112
  recurrence5A0_coeff_113
  recurrence5A0_coeff_114
  recurrence5A0_coeff_115
  recurrence5A0_coeff_116
  recurrence5A0_coeff_117
  recurrence5A0_coeff_118
  recurrence5A0_coeff_119
  recurrence5A0_coeff_120
  recurrence5A0_coeff_121
  recurrence5A0_coeff_122
  recurrence5A0_coeff_123
  recurrence5A0_coeff_124
  recurrence5A0_coeff_125
  recurrence5A0_coeff_126
  recurrence5A0_coeff_127
  recurrence5A0_coeff_128
  recurrence5A0_coeff_129
  recurrence5A0_coeff_130
  recurrence5A0_coeff_131
  recurrence5A0_coeff_132
  recurrence5A0_coeff_133
  recurrence5A0_coeff_134
  recurrence5A0_coeff_135
  recurrence5A0_coeff_136
  recurrence5A0_coeff_137
  recurrence5A0_coeff_138
  recurrence5A0_coeff_139
  recurrence5A0_coeff_140
  recurrence5A0_coeff_141
  recurrence5A0_coeff_142
  recurrence5A0_coeff_143
  recurrence5A0_coeff_144
  recurrence5A0_coeff_145
  recurrence5A0_coeff_146
  recurrence5A0_coeff_147
  recurrence5A0_coeff_148
  recurrence5A0_coeff_149
  recurrence5A0_coeff_150
  recurrence5A0_coeff_151
  recurrence5A0_coeff_152
  recurrence5A0_coeff_153
  recurrence5A0_coeff_154
  recurrence5A0_coeff_155
  recurrence5A0_coeff_156

attribute [local simp]
  recurrence5A0_coeff_157
  recurrence5A0_coeff_158
  recurrence5A0_coeff_159
  recurrence5A0_coeff_160
  recurrence5A0_coeff_161
  recurrence5A0_coeff_162
  recurrence5A0_coeff_163
  recurrence5A0_coeff_164
  recurrence5A0_coeff_165
  recurrence5A0_coeff_166
  recurrence5A0_coeff_167
  recurrence5A0_coeff_168
  recurrence5A0_coeff_169
  recurrence5A0_coeff_170
  recurrence5A0_coeff_171
  recurrence5A0_coeff_172
  recurrence5A0_coeff_173
  recurrence5A0_coeff_174
  recurrence5A0_coeff_175
  recurrence5A0_coeff_176

theorem recurrence5Scalar0Left_coeff_117 :
    recurrence5Scalar0Left.coeff 117 =
      (((((226906576982902769573819907819831732393952253442 * 10 ^ 70 +
        8157292804935230793351874072552719426803000327158831871730392076409367) * 10 ^ 70 +
        5584733912569692911336666519317270212825603116931929472038530630091896) * 10 ^ 70 +
        2874807252129161273569662514445802055290917994669767708671689678795866) * 10 ^ 70 +
        4094661768644516685793256184239155827463694214808912559142273290578762) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_118 :
    recurrence5Scalar0Left.coeff 118 =
      -(((((1295393575595166891993788999058725022607948837329 * 10 ^ 70 +
        5027788769762047722823831850623989901236851974493344274519964285049166) * 10 ^ 70 +
        6338265427209098239266368670382321073881694517249800357832413262111461) * 10 ^ 70 +
        6400714990121137585373260026932998906436872237563053111764676966476210) * 10 ^ 70 +
        2773314918603045437927189041895077149939770519329097969188155240877127) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 0 +
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_119 :
    recurrence5Scalar0Left.coeff 119 =
      (((((7220907375928946582994186508733660241716594447730 * 10 ^ 70 +
        5936123522675737313725199084950316243077716642754426756878319336602113) * 10 ^ 70 +
        4089026878790580033527550842308737645075200157355637420255574574534881) * 10 ^ 70 +
        6840451808113118537700925005847711928953451173439170813681099146331198) * 10 ^ 70 +
        5112551340189592090224224524781654827042281687316073555977185906165082) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_120 :
    recurrence5Scalar0Left.coeff 120 =
      -(((((39310828647536974093233803804507150380310695380080 * 10 ^ 70 +
        3204865231043738904403787681710699202116467332049725193001184914793192) * 10 ^ 70 +
        3129510737400124989310442209135675737013984612358288512852064928367901) * 10 ^ 70 +
        3457323472579462205865908731894456639013697602827906797222215087893512) * 10 ^ 70 +
        9750215432252476040889577986531923731548276172323817335556517139258898) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_121 :
    recurrence5Scalar0Left.coeff 121 =
      (((((209052532729867511280412370863035055575585898082332 * 10 ^ 70 +
        8061923209510814868266004021089821701030138359571275677400891233788531) * 10 ^ 70 +
        9344469912549642318926722617536190629834225421494807583995763357624500) * 10 ^ 70 +
        4789455995303098932702190360487730549129634494036798491356186542777490) * 10 ^ 70 +
        9104458860880799987489734047951213468534870955676728477478815127305439) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_122 :
    recurrence5Scalar0Left.coeff 122 =
      -(((((1086204022514687796969654757946149432844798283117006 * 10 ^ 70 +
        0776175500062493775457312372481111477387302792269110308870217008774858) * 10 ^ 70 +
        3797729627414388360122660943459745365006766233797678249278252078705732) * 10 ^ 70 +
        0752667642242605752321806298543401534736749452342860247211713181851750) * 10 ^ 70 +
        8711040458440692778770411667712852685843226243452670047788360629649013) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_123 :
    recurrence5Scalar0Left.coeff 123 =
      (((((5515280916939256856548854216214239846590445615599123 * 10 ^ 70 +
        7082056948226599295404691426418629799103930075216679615248182346343390) * 10 ^ 70 +
        2930944579814648622818055446637273974054681261691304382344411170828075) * 10 ^ 70 +
        9296712340424951115909184899925825483855469322802111540523502074180031) * 10 ^ 70 +
        5217082181695144905653591476363703468735496999519501902152996029068794) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_124 :
    recurrence5Scalar0Left.coeff 124 =
      -(((((27372175622666757280426058878291506720124264463678838 * 10 ^ 70 +
        1549562123214764751230976500546208122737633904896460584410225811605202) * 10 ^ 70 +
        5754050579084429990458407436736130342077463124715999318533174574258933) * 10 ^ 70 +
        5724642059561611029960849972934141194757639982262359996689667841193499) * 10 ^ 70 +
        5868657186203030474779924822626719075658871811671529449418931961218664) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_125 :
    recurrence5Scalar0Left.coeff 125 =
      (((((132806516149240303883973238674233548769292716811445827 * 10 ^ 70 +
        2613811928428060826540408610950613699806493497160843438292947008167577) * 10 ^ 70 +
        8084372579317205403298431730735664115003125205720831489080383907290796) * 10 ^ 70 +
        4195723855954218568216427025197623186226212214350384416461080193476910) * 10 ^ 70 +
        3189144465895491908012636176038027547893181258270356399623344008295444) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_126 :
    recurrence5Scalar0Left.coeff 126 =
      -(((((630055186415656943827008025071968476240782908081807913 * 10 ^ 70 +
        7977533938511992938937457935898019023144033162491394929838380177719109) * 10 ^ 70 +
        2080412893252387010330831937714485700995077895513157348819020112399384) * 10 ^ 70 +
        0428519327793624433957473927928151826688325903946701070413900910384173) * 10 ^ 70 +
        1563536853245024185746993026137163891056668606336992361240588458570730) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_127 :
    recurrence5Scalar0Left.coeff 127 =
      (((((2923247414496158841264470583630133618090297304916309945 * 10 ^ 70 +
        0544729264720948861676377947444306683388453980917496118082343283428517) * 10 ^ 70 +
        2962515952517270246945239662306801504824941196260886115681782976448434) * 10 ^ 70 +
        6915629145050550179703085849125463962056434144132472120059792267346792) * 10 ^ 70 +
        3178845159764175554511093925266707648481837857095577993787748994748026) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_128 :
    recurrence5Scalar0Left.coeff 128 =
      -(((((13266516929997293571507519093362820917013570933542928112 * 10 ^ 70 +
        0338121202660251297039021937116902270636379357872961229431775421114426) * 10 ^ 70 +
        4543944004502996916102040104710628394340505635852497132107749698198684) * 10 ^ 70 +
        2358208087921269630906073801265070468368720463521562686227745543615708) * 10 ^ 70 +
        7800150543160908320274179030404425486286687890868730643903842586645709) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_129 :
    recurrence5Scalar0Left.coeff 129 =
      (((((58901614713113067004960705574613238052649850715278123146 * 10 ^ 70 +
        2218644068932649407863007296693962559050248144067926974226329700596682) * 10 ^ 70 +
        2218983804437826373796139840307345850449878376429067076927407156781877) * 10 ^ 70 +
        8886167146880348063378668855310769518228441504733655983583237042432896) * 10 ^ 70 +
        6985697556976045506964547667534727307464503213269538383135287427121365) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_130 :
    recurrence5Scalar0Left.coeff 130 =
      -(((((255887502611396841172453476245184419545595900304101882333 * 10 ^ 70 +
        5612502821525190890189904518944909517142544653677914734673735453484247) * 10 ^ 70 +
        9958619866120081656233252565132953316867576937908815478952900589657697) * 10 ^ 70 +
        3928821662502964568850168520796495125238615801691666520385511392302092) * 10 ^ 70 +
        2164583517771402789805789470763970499075453480252242629410895605964655) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_131 :
    recurrence5Scalar0Left.coeff 131 =
      (((((1087910835617723102300993370657197250087801585914075690285 * 10 ^ 70 +
        7924775065009594992522451440429958495864712378426606231237382278965180) * 10 ^ 70 +
        2017154790512549120868722372468169988206457460035298029055462057717930) * 10 ^ 70 +
        8793507015443684309995534051597698482408474619953589302806926271784155) * 10 ^ 70 +
        3167127303419164741432670222820361349013164354476145194714142547846633) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_132 :
    recurrence5Scalar0Left.coeff 132 =
      -(((((4527190904961873783864530094979285748382232778497897693213 * 10 ^ 70 +
        5708767568372836321798174144016070785455427618570086719012818790622224) * 10 ^ 70 +
        6099425668630729240558930394929902746097340840686244987085971764078809) * 10 ^ 70 +
        9633935768610664856233948446312264182956610305512017823546164438380545) * 10 ^ 70 +
        4448193868084693509370725254412236215083520749369804844384428711865876) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_133 :
    recurrence5Scalar0Left.coeff 133 =
      (((((18442625110990935806115246229874618966621516893468041597584 * 10 ^ 70 +
        8105367056886520146208389288344889211804182774819425339608353824545830) * 10 ^ 70 +
        8336961365090822691292815735192915095271271082249373771092516186529301) * 10 ^ 70 +
        6114062922992163572794354625700932023402331703736978257377356123687000) * 10 ^ 70 +
        2959223372497845862108640179837191054480526747404629093769970223053800) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_134 :
    recurrence5Scalar0Left.coeff 134 =
      -(((((73559793366677349959122504029562433436758010213304060502656 * 10 ^ 70 +
        8048019873413650876216639893470115267880412254257848930678125666856327) * 10 ^ 70 +
        7773850250698658977277251735240726294799224379051458615405714403903637) * 10 ^ 70 +
        2433915103870651227687339169833179602454240091990463216491818142717206) * 10 ^ 70 +
        1530651747433453948063946396185002171232672616840296280283282669858106) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 0 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_135 :
    recurrence5Scalar0Left.coeff 135 =
      (((((287306740183365147398510892190969194008812547041978744614997 * 10 ^ 70 +
        4762880716462148654991925955969163857762498850001840712408410495481766) * 10 ^ 70 +
        9476736062962349261140888749405936094731622328213136248023140384497573) * 10 ^ 70 +
        5945570164930678400490303892506830647851057637161017654402300597501540) * 10 ^ 70 +
        0770951287111028331284631906202159336949585735850409617363266035304385) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_136 :
    recurrence5Scalar0Left.coeff 136 =
      -(((((1099007749838935790394360447392774029492621079531612153609567 * 10 ^ 70 +
        6456147271019541900988069616349263400295374984576939696520812160541030) * 10 ^ 70 +
        5623559461254825315865560819850897513810490292769937983230304906317914) * 10 ^ 70 +
        3557932684427816186911850106083294556716201386247031685760620522406631) * 10 ^ 70 +
        0694056501912464907085563517694057484083659433721504619543758380763314) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_137 :
    recurrence5Scalar0Left.coeff 137 =
      (((((4117805174417352734487497066469600559992095519537028442451786 * 10 ^ 70 +
        8243738599257221912885570808398527727954895311565148459007596054292716) * 10 ^ 70 +
        5479760005954287815687845053199184247589377115626244879242668227869061) * 10 ^ 70 +
        6855279295703423099523433483073942437984585633532910812598580070820134) * 10 ^ 70 +
        7217723121298222871002821675687932706454081212039399014603111776798922) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_138 :
    recurrence5Scalar0Left.coeff 138 =
      -(((((15114711051583203728676514177351952901698288449806818174324020 * 10 ^ 70 +
        3578891854389068127771849661500709096942806359759986706610539213584877) * 10 ^ 70 +
        5153048320159269455447807235772123856197056079525275181523228235684259) * 10 ^ 70 +
        3854513902581021246217178381268928929747574223595103790290596569126829) * 10 ^ 70 +
        6534171082015392302696435802424701524878363824946248616626107832584637) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_139 :
    recurrence5Scalar0Left.coeff 139 =
      (((((54357605027428371393964587231300672937773061169266797056145458 * 10 ^ 70 +
        5123771717956110233255158353634819591980960483539122311373948711321582) * 10 ^ 70 +
        3609722257338179142299779830569253703433015074092819940952983143143456) * 10 ^ 70 +
        5080318660730138846093363784544030329755513645520107117423404170831565) * 10 ^ 70 +
        2424807289503589179706836976680299035212382150311468040688169520707048) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_140 :
    recurrence5Scalar0Left.coeff 140 =
      -(((((191559240480450068409955307652185486588658810094650880228000187 * 10 ^ 70 +
        1204607751599600601674127532824060077417834238930861030981522494025779) * 10 ^ 70 +
        8608370233160649546443356864994721368051513842732278826632097480474427) * 10 ^ 70 +
        2532906740369975771843136925750888889581820655042899586636391207716498) * 10 ^ 70 +
        7391796309541534809316758561068928100468050608960144888541908973720951) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_141 :
    recurrence5Scalar0Left.coeff 141 =
      (((((661580515326278055390595388531406692549861944634300905347471711 * 10 ^ 70 +
        0694018875969657166675905433788689291287126810573153255582520973279656) * 10 ^ 70 +
        0658916261611804678512056074021890618355098002312773971590344014115017) * 10 ^ 70 +
        0484801471123098970997246491438504486922087093048232382711795108532482) * 10 ^ 70 +
        1157908205262705276098033121450291780342466610439446738097986477703792) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_142 :
    recurrence5Scalar0Left.coeff 142 =
      -(((((2239505788928877182485851208025960689342617729880384870646099093 * 10 ^ 70 +
        4555101477224216948797303000542827254058884494386928682595907738645318) * 10 ^ 70 +
        1622367533421080636587464589607779937330241074665316338193765969327747) * 10 ^ 70 +
        3655777890809399094409909826199273313622680292592699152125548550087314) * 10 ^ 70 +
        0558602915320048119709806695789077474380137525564521173322512464485034) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_143 :
    recurrence5Scalar0Left.coeff 143 =
      (((((7431273902346111085242722121920266736468824979187939241512382566 * 10 ^ 70 +
        6633436766958200293641204184141965460649857160032455423689472097141317) * 10 ^ 70 +
        0242092022300194377865182878492812212488013818364759821126395047816392) * 10 ^ 70 +
        5264277156486060098094244778691842013794358812022469579009094999463980) * 10 ^ 70 +
        6166000530767848860143574408150039902411934310426843925208936264830163) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_144 :
    recurrence5Scalar0Left.coeff 144 =
      -(((((24174991389582422953043897634224708735665121232061289918257080852 * 10 ^ 70 +
        2321929729611444818010571447282403178511675034411193532916133992830218) * 10 ^ 70 +
        5556669753644846742535789952277159218827075487979247457532953380071720) * 10 ^ 70 +
        3447049684975948281942480804825172790981113154454977264361339850979248) * 10 ^ 70 +
        8476883333745837362413817074282830512041573661504838064359486609815520) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_145 :
    recurrence5Scalar0Left.coeff 145 =
      (((((77109956352990620623776790682278256026126971797327901647366849929 * 10 ^ 70 +
        7136760426595571323233524352122471638977504249051066717010065228609571) * 10 ^ 70 +
        7100147729007364832030176048619959284777969423829192114730159325244391) * 10 ^ 70 +
        8511158124249737767758184561093735021887057361504535836160679265499166) * 10 ^ 70 +
        6918852619438379537187701024305684316556042117831616042072390019793438) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 0 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_146 :
    recurrence5Scalar0Left.coeff 146 =
      -(((((241181220012491520758232513695817193529229232348427518074676088146 * 10 ^ 70 +
        5745342443285466002034925968811660637632347785340200247419152325583714) * 10 ^ 70 +
        9631573929318225556890629895380749392589079765323103212160700772921418) * 10 ^ 70 +
        6875377185756510812755429957471314218675650333553889962617053931413718) * 10 ^ 70 +
        3259694632502842626477775534197583074571570967123912847995460907264998) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_147 :
    recurrence5Scalar0Left.coeff 147 =
      (((((739796078608146871648016518108372726402337597013593268357145299974 * 10 ^ 70 +
        2884768675979314103218140438792565917647511518314094326061007723793686) * 10 ^ 70 +
        5970379727662912075425282197154957000036054963776966142108358516398699) * 10 ^ 70 +
        4776715890409160760503988149397497647786221747634165709207094929380557) * 10 ^ 70 +
        5633028960287958886333203499603200363272814809113812496503662465868693) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_148 :
    recurrence5Scalar0Left.coeff 148 =
      -(((((2225673638734850991129856740166601236681483957338345804387101041663 * 10 ^ 70 +
        4080982962658971917980803573257750939641922258395089880628824383858125) * 10 ^ 70 +
        8023994330854968265640653614400663877579950852351392582507952087003212) * 10 ^ 70 +
        7663126557077034387312360512580997708843579002805430366688410669820815) * 10 ^ 70 +
        1040530282545449700789964448858181742723263723133268146595832689743119) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_149 :
    recurrence5Scalar0Left.coeff 149 =
      (((((6568044870039980961358024272479733307060518726652450865479876651832 * 10 ^ 70 +
        7741492169524438003113715043031706246082845238706492163139042641255865) * 10 ^ 70 +
        4014914168077820689007159328374445619998888211442439198454843954067031) * 10 ^ 70 +
        0838647430330401009252867019111064863566266439997033450445313838128384) * 10 ^ 70 +
        3759957193179275636040442507281668000793326742880912631577505064883773) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_150 :
    recurrence5Scalar0Left.coeff 150 =
      -(((((19014242787960004437760329336045641111916453556858372546386180839181 * 10 ^ 70 +
        6530419647970985370312243267209026161292048175111257695456811350517809) * 10 ^ 70 +
        8203891685157564819426967861780440261291410742235247804662613738765732) * 10 ^ 70 +
        5742130047026926191400606390635788205700158673711615702468342828180306) * 10 ^ 70 +
        7465316056590193541250734977747516875339124260767430285269777117542267) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_151 :
    recurrence5Scalar0Left.coeff 151 =
      (((((54004789540578122315711662927869256536680586604111896597269299924515 * 10 ^ 70 +
        6817664940255156406648771597501311253117339979324677213550626691829951) * 10 ^ 70 +
        9668039643357896909150604338463311518040047282988892073629612817009080) * 10 ^ 70 +
        7993168752767546959029724402153987795794535216090461976126874036427500) * 10 ^ 70 +
        0032951501651991177197104235294838628942633866987101511535800266522459) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_152 :
    recurrence5Scalar0Left.coeff 152 =
      -(((((150500102257360490348103497645891416353977058160285215178086364795599 * 10 ^ 70 +
        7780345134511857838681394977187840794367033229654466745275925833412735) * 10 ^ 70 +
        7849243453390251864157397850243151621358655041122186209893341530006195) * 10 ^ 70 +
        8916426536428791421586539887299203668211948454882049967155342231943267) * 10 ^ 70 +
        0462573649174124987324752017752014139573536317317979246692037177363828) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_153 :
    recurrence5Scalar0Left.coeff 153 =
      (((((411559377442294906789188963135303821355479362623328972221143758142361 * 10 ^ 70 +
        3939379855093733019228130619751390590393147510985467046065347679161423) * 10 ^ 70 +
        8292031794880196669417655729699211663096562460764808558832864166537573) * 10 ^ 70 +
        7666202505481510988453981221689222271841174482519064766404675107283967) * 10 ^ 70 +
        1013205004205049247871273894147016199046572908683636311975907089202913) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_154 :
    recurrence5Scalar0Left.coeff 154 =
      -(((((1104481133954230204221109014334834218180882487955807364289476376868598 * 10 ^ 70 +
        7619267330294195953302670438145488308498580579677290204997076601108741) * 10 ^ 70 +
        8292378311520483145799189958089453478351421502379291702688425884402027) * 10 ^ 70 +
        9720019420785603462681832493928282745827724821265846644245205313265290) * 10 ^ 70 +
        5943325501565465605152616318322424950859233467569288549644685384863804) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_155 :
    recurrence5Scalar0Left.coeff 155 =
      (((((2909056236261290556617419274207773863398243816571295495178395715344758 * 10 ^ 70 +
        0373591375684247466234762909560524378032024291475419649592399479881879) * 10 ^ 70 +
        3439085702525275228471058057666101649451192765192601635922512920625187) * 10 ^ 70 +
        1234673447493619106024138215617259367510077524709960158131412686790947) * 10 ^ 70 +
        3835040417933160672481832345759871647657399522848854765180698538324308) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_156 :
    recurrence5Scalar0Left.coeff 156 =
      -(((((7520572654272745960494141525015791462333231454594020899195215196366352 * 10 ^ 70 +
        1328516637276822791909961445290759725954857944683774242462629094396344) * 10 ^ 70 +
        6316508054110554125606647196256619198587404914273296083449994660057796) * 10 ^ 70 +
        9946273303515346152549429297577502503068547321061011936300926920526344) * 10 ^ 70 +
        8186297534839265674409088388116691479968360595981772825992127762994469) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_157 :
    recurrence5Scalar0Left.coeff 157 =
      ((((((1 * 10 ^ 70 +
        9084936545748565386176592247122015324864631119577580399839820757635152) * 10 ^ 70 +
        4098653696048643995301717805606436952148631555079528653961527357447070) * 10 ^ 70 +
        6807722098470181356850214757128778150600760816334641728046960267249960) * 10 ^ 70 +
        0249208820014670197534413321633912741964736097242365701419499693327263) * 10 ^ 70 +
        8584395742699374798033981525410076386311746065537076523278249577534241) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_158 :
    recurrence5Scalar0Left.coeff 158 =
      -((((((4 * 10 ^ 70 +
        7545199730143107258860476845010223869546966378302683502688789334205672) * 10 ^ 70 +
        8547924360229966870363336841847923944221720747027038186942293021306112) * 10 ^ 70 +
        1638451085482663845531415974495974290837613457152198027411685409651072) * 10 ^ 70 +
        2207174865274606688033512532534441785057938621868467370295334220939883) * 10 ^ 70 +
        6795513309625464403059264627240763036140391645129538071053049958259695) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar0Left_coeff_159 :
    recurrence5Scalar0Left.coeff 159 =
      ((((((11 * 10 ^ 70 +
        6287499653153657042443418105525840216051229715036506473208630269814718) * 10 ^ 70 +
        7029440955624347126796015733874723525323117506246331986667208057488004) * 10 ^ 70 +
        0386552649683098238530886504784019221445701509145853078107292990439359) * 10 ^ 70 +
        5545589744989717459532344730499345349825544872580148795054027746807092) * 10 ^ 70 +
        5730372482768854485581423850706537018915037174304450679813158190576719) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
