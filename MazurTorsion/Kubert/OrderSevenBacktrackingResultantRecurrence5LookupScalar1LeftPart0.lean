/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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
  recurrence5A1_coeff_0
  recurrence5A1_coeff_1
  recurrence5A1_coeff_2
  recurrence5A1_coeff_3
  recurrence5A1_coeff_4
  recurrence5A1_coeff_5
  recurrence5A1_coeff_6
  recurrence5A1_coeff_7
  recurrence5A1_coeff_8
  recurrence5A1_coeff_9
  recurrence5A1_coeff_10
  recurrence5A1_coeff_11
  recurrence5A1_coeff_12
  recurrence5A1_coeff_13
  recurrence5A1_coeff_14
  recurrence5A1_coeff_15
  recurrence5A1_coeff_16
  recurrence5A1_coeff_17
  recurrence5A1_coeff_18
  recurrence5A1_coeff_19
  recurrence5A1_coeff_20
  recurrence5A1_coeff_21
  recurrence5A1_coeff_22
  recurrence5A1_coeff_23
  recurrence5A1_coeff_24
  recurrence5A1_coeff_25
  recurrence5A1_coeff_26
  recurrence5A1_coeff_27
  recurrence5A1_coeff_28

attribute [local simp]
  recurrence5A1_coeff_29
  recurrence5A1_coeff_30
  recurrence5A1_coeff_31
  recurrence5A1_coeff_32
  recurrence5A1_coeff_33
  recurrence5A1_coeff_34
  recurrence5A1_coeff_35
  recurrence5A1_coeff_36
  recurrence5A1_coeff_37
  recurrence5A1_coeff_38
  recurrence5A1_coeff_39
  recurrence5A1_coeff_40
  recurrence5A1_coeff_41
  recurrence5A1_coeff_42
  recurrence5A1_coeff_43
  recurrence5A1_coeff_44
  recurrence5A1_coeff_45
  recurrence5A1_coeff_46
  recurrence5A1_coeff_47
  recurrence5A1_coeff_48
  recurrence5A1_coeff_49
  recurrence5A1_coeff_50
  recurrence5A1_coeff_51
  recurrence5A1_coeff_52
  recurrence5A1_coeff_53
  recurrence5A1_coeff_54
  recurrence5A1_coeff_55
  recurrence5A1_coeff_56
  recurrence5A1_coeff_57
  recurrence5A1_coeff_58
  recurrence5A1_coeff_59
  recurrence5A1_coeff_60
  recurrence5A1_coeff_61
  recurrence5A1_coeff_62
  recurrence5A1_coeff_63
  recurrence5A1_coeff_64
  recurrence5A1_coeff_65
  recurrence5A1_coeff_66
  recurrence5A1_coeff_67
  recurrence5A1_coeff_68
  recurrence5A1_coeff_69
  recurrence5A1_coeff_70
  recurrence5A1_coeff_71
  recurrence5A1_coeff_72
  recurrence5A1_coeff_73
  recurrence5A1_coeff_74
  recurrence5A1_coeff_75
  recurrence5A1_coeff_76
  recurrence5A1_coeff_77
  recurrence5A1_coeff_78
  recurrence5A1_coeff_79
  recurrence5A1_coeff_80
  recurrence5A1_coeff_81
  recurrence5A1_coeff_82
  recurrence5A1_coeff_83
  recurrence5A1_coeff_84
  recurrence5A1_coeff_85
  recurrence5A1_coeff_86
  recurrence5A1_coeff_87
  recurrence5A1_coeff_88
  recurrence5A1_coeff_89
  recurrence5A1_coeff_90
  recurrence5A1_coeff_91
  recurrence5A1_coeff_92

attribute [local simp]
  recurrence5A1_coeff_93
  recurrence5A1_coeff_94
  recurrence5A1_coeff_95
  recurrence5A1_coeff_96
  recurrence5A1_coeff_97
  recurrence5A1_coeff_98
  recurrence5A1_coeff_99
  recurrence5A1_coeff_100
  recurrence5A1_coeff_101
  recurrence5A1_coeff_102
  recurrence5A1_coeff_103
  recurrence5A1_coeff_104
  recurrence5A1_coeff_105
  recurrence5A1_coeff_106
  recurrence5A1_coeff_107
  recurrence5A1_coeff_108
  recurrence5A1_coeff_109
  recurrence5A1_coeff_110
  recurrence5A1_coeff_111
  recurrence5A1_coeff_112
  recurrence5A1_coeff_113
  recurrence5A1_coeff_114
  recurrence5A1_coeff_115
  recurrence5A1_coeff_116
  recurrence5A1_coeff_117
  recurrence5A1_coeff_118
  recurrence5A1_coeff_119
  recurrence5A1_coeff_120
  recurrence5A1_coeff_121
  recurrence5A1_coeff_122
  recurrence5A1_coeff_123
  recurrence5A1_coeff_124
  recurrence5A1_coeff_125
  recurrence5A1_coeff_126
  recurrence5A1_coeff_127
  recurrence5A1_coeff_128
  recurrence5A1_coeff_129
  recurrence5A1_coeff_130
  recurrence5A1_coeff_131
  recurrence5A1_coeff_132
  recurrence5A1_coeff_133
  recurrence5A1_coeff_134
  recurrence5A1_coeff_135
  recurrence5A1_coeff_136
  recurrence5A1_coeff_137
  recurrence5A1_coeff_138
  recurrence5A1_coeff_139
  recurrence5A1_coeff_140
  recurrence5A1_coeff_141
  recurrence5A1_coeff_142
  recurrence5A1_coeff_143
  recurrence5A1_coeff_144
  recurrence5A1_coeff_145
  recurrence5A1_coeff_146
  recurrence5A1_coeff_147
  recurrence5A1_coeff_148
  recurrence5A1_coeff_149
  recurrence5A1_coeff_150
  recurrence5A1_coeff_151
  recurrence5A1_coeff_152
  recurrence5A1_coeff_153
  recurrence5A1_coeff_154
  recurrence5A1_coeff_155
  recurrence5A1_coeff_156

attribute [local simp]
  recurrence5A1_coeff_157
  recurrence5A1_coeff_158
  recurrence5A1_coeff_159
  recurrence5A1_coeff_160
  recurrence5A1_coeff_161
  recurrence5A1_coeff_162
  recurrence5A1_coeff_163
  recurrence5A1_coeff_164
  recurrence5A1_coeff_165
  recurrence5A1_coeff_166
  recurrence5A1_coeff_167
  recurrence5A1_coeff_168
  recurrence5A1_coeff_169
  recurrence5A1_coeff_170
  recurrence5A1_coeff_171
  recurrence5A1_coeff_172

theorem recurrence5Scalar1Left_coeff_0 :
    recurrence5Scalar1Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_1 :
    recurrence5Scalar1Left.coeff 1 =
      ((3086656350854110639262994968440822964502465198252869400 * 10 ^ 70 +
        1256197002532114134791933149230308636977887967923712646303834569342976) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_2 :
    recurrence5Scalar1Left.coeff 2 =
      -((2231432058547180651775018376380347644615932360421404559815 * 10 ^ 70 +
        4572806371896164234453872203065479645008396183899811056279151032995840) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_3 :
    recurrence5Scalar1Left.coeff 3 =
      ((56226046642816714291467602593912238639756799954535605680760154 * 10 ^ 70 +
        2010611875264931475404412107366189979376498511586992787517315022520960) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_4 :
    recurrence5Scalar1Left.coeff 4 =
      -((177398503383366222079472448481089464751654353776993177184459769048 * 10 ^ 70 +
        9364035060062293464993743776706080564012919859525807728606769600986528) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_5 :
    recurrence5Scalar1Left.coeff 5 =
      ((522598617032198816837198956864330477339576430215271972647817712950758 * 10 ^ 70 +
        6214276380771372444834608261239342303421889670240907326538931612133024) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_6 :
    recurrence5Scalar1Left.coeff 6 =
      -(((164 * 10 ^ 70 +
        9869148785711596280379624839141341144089391662828403288653157985671649) * 10 ^ 70 +
        1695267691404052447130450266967776267797052579023896423237325148752384) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_7 :
    recurrence5Scalar1Left.coeff 7 =
      (((404220 * 10 ^ 70 +
        1332756302444433784401153427408693953726664647853064932520389957003322) * 10 ^ 70 +
        4445929277051688511708896384930376753296993410310691785086131071208320) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_8 :
    recurrence5Scalar1Left.coeff 8 =
      -(((680420248 * 10 ^ 70 +
        9847045071045833247982195358548888112126322880702448606627290539836081) * 10 ^ 70 +
        9278819695258064416229255756245874777819590019705730717912882097221472) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_9 :
    recurrence5Scalar1Left.coeff 9 =
      (((801298927540 * 10 ^ 70 +
        7626523167106104409037904208781104768932084822361743603095699980619253) * 10 ^ 70 +
        7382427186439532708870853480529561188824066520451926871090964628948688) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_10 :
    recurrence5Scalar1Left.coeff 10 =
      -(((648366306974043 * 10 ^ 70 +
        8703368819998256890624965033060086522940018085451392825089449261667282) * 10 ^ 70 +
        6292052646433454457555138385105251249139240476765044778154447606652352) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_11 :
    recurrence5Scalar1Left.coeff 11 =
      (((315439532692324802 * 10 ^ 70 +
        7022588695676748381957389714906215723536786025847420242511738598702657) * 10 ^ 70 +
        1787259450267215270400509600039192421026665923046376613155023666927344) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_12 :
    recurrence5Scalar1Left.coeff 12 =
      -(((13142851898173189295 * 10 ^ 70 +
        8695787840030446294595516688823588660009063567584006769056294678828852) * 10 ^ 70 +
        6514895865411585035396395275804508669806670884930338763814158783514336) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_13 :
    recurrence5Scalar1Left.coeff 13 =
      -(((125007631942181449112618 * 10 ^ 70 +
        4951773925484508674979831776494556100109047566532691846190297499456315) * 10 ^ 70 +
        8572825514217574077698566517953915594487885207955269542070008041868544) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_14 :
    recurrence5Scalar1Left.coeff 14 =
      (((116992015771392833169072028 * 10 ^ 70 +
        7241368943771502850117680103847689117144770350372959444995390787850772) * 10 ^ 70 +
        2193228857248542766336859141586283007513839176835419744818755098143456) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_15 :
    recurrence5Scalar1Left.coeff 15 =
      -(((55933994577405339948749615200 * 10 ^ 70 +
        3681154452072034208524362013172946036409126706262202617747880784512239) * 10 ^ 70 +
        0555637001533552910002858505027545311910420175771477405010543828356928) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_16 :
    recurrence5Scalar1Left.coeff 16 =
      (((10097176407150087693107634721254 * 10 ^ 70 +
        3255968420500565804936049671328017434885230679737602508361484540462670) * 10 ^ 70 +
        6934529758363145599034614940508310658486263149813217470742450889870952) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_17 :
    recurrence5Scalar1Left.coeff 17 =
      (((6060158383945784605098527057634460 * 10 ^ 70 +
        3593730659215625579600973745560545868927759281403941319901213434770122) * 10 ^ 70 +
        7679053777708916152829292525552247411967536141009985395809948094953176) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_18 :
    recurrence5Scalar1Left.coeff 18 =
      -(((5777930950310907757299699031622168415 * 10 ^ 70 +
        7770959792425274185870454079135980434463824424225464383593104206481609) * 10 ^ 70 +
        3520503080780400021220887039484597559354335538974780504243716377172232) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_19 :
    recurrence5Scalar1Left.coeff 19 =
      (((2200742154501721528817721526805573454830 * 10 ^ 70 +
        5742526451861636619525499027664606973366239322038234051706674539962873) * 10 ^ 70 +
        7027889097350344142257146299415952124463003705711648139344218927537728) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_20 :
    recurrence5Scalar1Left.coeff 20 =
      -(((209890737033223752000988880179761537571133 * 10 ^ 70 +
        5787274670495356607626775837521497168299599955251513513901385224552142) * 10 ^ 70 +
        7096916534021898994805063029623638080558214174619096785799325032592928) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_21 :
    recurrence5Scalar1Left.coeff 21 =
      -(((243751560287264830993631968869792153978510075 * 10 ^ 70 +
        3593331025594787893893013614311589692385184886968163088612098361104539) * 10 ^ 70 +
        2413253378153545806224471332875835186301461777202928664116226546961668) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_22 :
    recurrence5Scalar1Left.coeff 22 =
      (((153865790827388751149729345777837338217924501373 * 10 ^ 70 +
        6885245966352872872222163668539213467783026796731085229347969106986593) * 10 ^ 70 +
        5044364002980416158644494672852186374863570089719990318803446128243734) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_23 :
    recurrence5Scalar1Left.coeff 23 =
      -(((37458851330682832057334914941322028021877778506971 * 10 ^ 70 +
        0775442685279652579555568402016788398982059202952367872799713140641590) * 10 ^ 70 +
        8787053427211428108611079524766789012539779029661712577557977029815022) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_24 :
    recurrence5Scalar1Left.coeff 24 =
      -(((7013830521382793236429585842271608395014269845634754 * 10 ^ 70 +
        6804137365557225358987264500414364738329811241369505125005876944310518) * 10 ^ 70 +
        3142951483360757558187609947063111770639168415285459255668750993990658) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_25 :
    recurrence5Scalar1Left.coeff 25 =
      (((11464252273295846993918568453864482606168766372086746930 * 10 ^ 70 +
        8802824415821533483878282282184678514445765562532674779143022983958808) * 10 ^ 70 +
        2587932036422598324448391395426730510661420569605538523203926034569442) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_26 :
    recurrence5Scalar1Left.coeff 26 =
      -(((6450097424067330963253385240620665433283593997190882849164 * 10 ^ 70 +
        2266161368247742993435252254370542012866574451904499870754548027494614) * 10 ^ 70 +
        8893087041706834565648402578454935583093470767799488108883652229400210) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_27 :
    recurrence5Scalar1Left.coeff 27 =
      (((2561230777771972916894640471801894113560933079035137049530620 * 10 ^ 70 +
        6823260409202698819254038954051135160624812297486708725423818331338241) * 10 ^ 70 +
        3574065278802589097556034296024151389134547288744005986392851989379173) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_28 :
    recurrence5Scalar1Left.coeff 28 =
      -(((814101001460288237951948561082327537467271461308170506439667338 * 10 ^ 70 +
        8090646152830859373347622423923945391691026631922141716425898190099659) * 10 ^ 70 +
        2807925971445060429853399750142312006251159624580162484481781856092206) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_29 :
    recurrence5Scalar1Left.coeff 29 =
      (((217423448327115676420295645891858195471002088785997772408583029957 * 10 ^ 70 +
        8190879721684326695875766973643624248558527016315014886508658597740257) * 10 ^ 70 +
        3775560426016562138679433714198264545744550665094655975206928429185834) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_30 :
    recurrence5Scalar1Left.coeff 30 =
      -(((49974567634561128519248430527132029038753655095712915462366900092521 * 10 ^ 70 +
        7167824248325133002320532441839680474577686831639846824116467837372598) * 10 ^ 70 +
        9814679934088664824739439270010453894481908561616037704640373937564098) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_31 :
    recurrence5Scalar1Left.coeff 31 =
      ((((1 * 10 ^ 70 +
        0012680763840105287272573834295435619011747141763743769030185698320517) * 10 ^ 70 +
        7953946674615130860742451908513543462803390668088477375011778795511774) * 10 ^ 70 +
        6651530813680464951256967736130784012408140488923427158617328892961786) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_32 :
    recurrence5Scalar1Left.coeff 32 =
      -((((175 * 10 ^ 70 +
        8871152883045459693415720912452141829056151400134525793372582195210246) * 10 ^ 70 +
        7620742904740427902113771351583766377328808838333231301843900405492224) * 10 ^ 70 +
        6440838293551530141161561678276270195175297509376121500586871120158768) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_33 :
    recurrence5Scalar1Left.coeff 33 =
      ((((27080 * 10 ^ 70 +
        9906994019229990299707444415298237530319575898315515201908821634970542) * 10 ^ 70 +
        9418910300168166385157993857851376578724905656936073896232153236419215) * 10 ^ 70 +
        1613923726624965474875370376133072596341840096614804551214327435475369) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_34 :
    recurrence5Scalar1Left.coeff 34 =
      -((((3624293 * 10 ^ 70 +
        3512637490854399102653708145775268024698163161337997736202958964044960) * 10 ^ 70 +
        5746835714543438847290772771404870012117483955036031416161346757800426) * 10 ^ 70 +
        9208015058228288820988156670197777151693161517495966139316975996796523) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_35 :
    recurrence5Scalar1Left.coeff 35 =
      ((((411803608 * 10 ^ 70 +
        7941083126010360646771396492315630305810818225026053572575743392504235) * 10 ^ 70 +
        1770422358917278775562211077394186022786428134024494908977254474181195) * 10 ^ 70 +
        3948860904304828503902770645025903680675646589310896368220305725839589) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_36 :
    recurrence5Scalar1Left.coeff 36 =
      -((((37240526526 * 10 ^ 70 +
        9307499906734662853653516935526306956979084595217560626295491246503665) * 10 ^ 70 +
        4287667117491629930590237284777446461289610681282258244748939911134068) * 10 ^ 70 +
        7278313122574127720425485678103260850274587272043455172762297485996831) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_37 :
    recurrence5Scalar1Left.coeff 37 =
      ((((2077400191390 * 10 ^ 70 +
        7745892643729211355036796836085345953294055292410599586018814138373900) * 10 ^ 70 +
        6630580571503789981172565868249142985468818700890121548198836947926893) * 10 ^ 70 +
        4746239112374010403681829876900688289971984755281908485365941141114265) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_38 :
    recurrence5Scalar1Left.coeff 38 =
      ((((89095396350561 * 10 ^ 70 +
        6400933788637738367435006723739726988397811334437842325857745340027855) * 10 ^ 70 +
        0106847636868667145854876092553525407366008793340114217807576168179852) * 10 ^ 70 +
        5503882419134331605346408169440428888776794050061948153471920882576587) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_39 :
    recurrence5Scalar1Left.coeff 39 =
      -((((48422807070362751 * 10 ^ 70 +
        6285105026334278428170773229310736997947210192803715432283029830664229) * 10 ^ 70 +
        7178372485953641085334960829738661320823033605977008159771975249467425) * 10 ^ 70 +
        6368401524094384646106031172491537630762302389988464661323391026462553) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_40 :
    recurrence5Scalar1Left.coeff 40 =
      ((((9079592097551388175 * 10 ^ 70 +
        5575286825462075559465787952013703510710109325371845880382623921190831) * 10 ^ 70 +
        3261387298824586143018340563175158625283518677042993404386558177189260) * 10 ^ 70 +
        6314941042081920904237053541637178231055521281945739935410344357362792) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_41 :
    recurrence5Scalar1Left.coeff 41 =
      -((((1275610319613009714845 * 10 ^ 70 +
        9037916426601785627790819676814654337578837686320288106444107412201286) * 10 ^ 70 +
        5173468021226458475829471415071851544574078192203625281416728692062767) * 10 ^ 70 +
        5627105300563462214529630825994549851025083850821285306037678654652653) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_42 :
    recurrence5Scalar1Left.coeff 42 =
      ((((151537692683724345236695 * 10 ^ 70 +
        3908626424471224549070432187788210454114225589070626813040470313300398) * 10 ^ 70 +
        5518352199821520171025061427542873649482081185204795981612947735277921) * 10 ^ 70 +
        7659837852417828776611698013674700573412603468604697875268437177052918) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_43 :
    recurrence5Scalar1Left.coeff 43 =
      -((((15905984320385679504564443 * 10 ^ 70 +
        2790668433807241962360867162139811398242864910735815085497864102499203) * 10 ^ 70 +
        4206542683637633504293805257366583340593626709428863246457515671229903) * 10 ^ 70 +
        0835288746756149961430739382933593450686483907223824985598519222056045) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_44 :
    recurrence5Scalar1Left.coeff 44 =
      ((((1507295796772873502297228436 * 10 ^ 70 +
        3539988625293839655749310569595915394782954346922006762881182333119787) * 10 ^ 70 +
        5589065585612818812471854923453077728905543322568379291426682284904585) * 10 ^ 70 +
        0693936742286487750437906925905900465037366599922590310136286907972004) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_45 :
    recurrence5Scalar1Left.coeff 45 =
      -((((130579932012277459826057839633 * 10 ^ 70 +
        6311411404511829899620163275063637466305861565387740462993744397520447) * 10 ^ 70 +
        6376208231973511335201682876370570667858242940332413072440835688251939) * 10 ^ 70 +
        6201951339478482538170493759579784633886869604376693573454684873554534) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_46 :
    recurrence5Scalar1Left.coeff 46 =
      ((((10426417536750729957986484246443 * 10 ^ 70 +
        2472563048203265981441104029014683657200156621157707580298765053719443) * 10 ^ 70 +
        5846517348611965077799646829145148636279541559278419501190252537071287) * 10 ^ 70 +
        5560015032230537968090588428101581252238322315394211786804684183004054) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_47 :
    recurrence5Scalar1Left.coeff 47 =
      -((((771740235487316538295437404870427 * 10 ^ 70 +
        8500773410535566110917445632046907395304491960827648584579502899375604) * 10 ^ 70 +
        6566331615305310696955282242791658132853415770222938270239739142818319) * 10 ^ 70 +
        5044650694547755143269892481589195117090205247665188005251786316955418) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_48 :
    recurrence5Scalar1Left.coeff 48 =
      ((((53180630854232734466305339650749262 * 10 ^ 70 +
        2766553064465758204952173786020337500004156187524171345434777611093119) * 10 ^ 70 +
        4574605397161510003168218660400628696364582989391687367051136549816514) * 10 ^ 70 +
        1255979558343348214685489877396812150870055005455574824838329389824966) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_49 :
    recurrence5Scalar1Left.coeff 49 =
      -((((3423310299913096352726922804873963522 * 10 ^ 70 +
        4952628936204478732416522816489345638560589972039122217506911121239085) * 10 ^ 70 +
        0674133773177168578150961445690177415330971234723059723616824632165079) * 10 ^ 70 +
        9694289913629300027937344490750679287943248328148832600589595509837987) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_50 :
    recurrence5Scalar1Left.coeff 50 =
      ((((206413037977171015525011459885853044487 * 10 ^ 70 +
        3106489353479561023747739243363961775967464611039866973767101266966756) * 10 ^ 70 +
        7572198100774846977049900480480547916997462763083879788791364192564233) * 10 ^ 70 +
        1768776245115290961732146628281012749364837044096333322601271606277837) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_51 :
    recurrence5Scalar1Left.coeff 51 =
      -((((11684642743384815814795202131478598138829 * 10 ^ 70 +
        0902388149926473845748025496569930790730255864540305950348527577124177) * 10 ^ 70 +
        1387292965500889572670655061455587384194438664565143152644256286152644) * 10 ^ 70 +
        1275246570918046866663052338453720473443787713709412771654966464268999) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_52 :
    recurrence5Scalar1Left.coeff 52 =
      ((((622188777291412292626204630519553424151703 * 10 ^ 70 +
        9904909737647295258900870585869579471291022586480139243025996325745962) * 10 ^ 70 +
        8889078639550214181051306942462296379180184553294518018305007302571760) * 10 ^ 70 +
        8550317925730167230750154556966867290173002307294261458441141047945403) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_53 :
    recurrence5Scalar1Left.coeff 53 =
      -((((31216394192859459034003366084053892227469998 * 10 ^ 70 +
        2717606603236070017434681032296724498689972168450719989756138811883774) * 10 ^ 70 +
        1159000851665913451826133347889320826047019208961149611168583870746591) * 10 ^ 70 +
        0934453425274423270103667249833535912863235493330890448530114718998790) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_54 :
    recurrence5Scalar1Left.coeff 54 =
      ((((1477845697386880136028096817797247290072105603 * 10 ^ 70 +
        9272590058880760711980626833405159205419847289516266049285176999544023) * 10 ^ 70 +
        6381920187821892915490982757990801543955569799085627963960798996727761) * 10 ^ 70 +
        3992994014242756097082089603255270038668443334483350585030156199400332) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_55 :
    recurrence5Scalar1Left.coeff 55 =
      -((((66102026502982462130226357995452620048570904639 * 10 ^ 70 +
        9183903757276778987804909170351708898011187639595282275816263199711913) * 10 ^ 70 +
        3895037375378844200697317552593397659808818115608090514397249153414088) * 10 ^ 70 +
        7387763579512612351022897773816527038648150525839985507687255117850489) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_56 :
    recurrence5Scalar1Left.coeff 56 =
      ((((2796565045058019630095408397563598558578453736892 * 10 ^ 70 +
        7497665802099751974858812910600628116810369867416138854851323562453628) * 10 ^ 70 +
        3598872933659376959808205818815952497977989366886875935327550499629628) * 10 ^ 70 +
        3801771212697850831132156436987679816947064734111839093232304035425691) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_57 :
    recurrence5Scalar1Left.coeff 57 =
      -((((112016657090091886344298977483391788951597906040657 * 10 ^ 70 +
        5910544754813821255951626664482102653830684387289170881580067530307411) * 10 ^ 70 +
        1106343232091839733238209658240440906750528264586454061554119682489087) * 10 ^ 70 +
        7756889210195235211494323799172502015842489718933710818931048077450164) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_58 :
    recurrence5Scalar1Left.coeff 58 =
      ((((4251597060970538230938216899660867462552474184961346 * 10 ^ 70 +
        2755810182189650120519206380369723501996284003482134107647172794098621) * 10 ^ 70 +
        9814646429514380320558394288842290713163191867950408558933999932012375) * 10 ^ 70 +
        6848170897392708009353472835889048823223931191720909561377195242709498) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_59 :
    recurrence5Scalar1Left.coeff 59 =
      -((((153016916990037720072121060077424758061983098636612915 * 10 ^ 70 +
        2626829946364490846580633314940829955882396567393547414122614650803724) * 10 ^ 70 +
        6360734651923679329538258336718380109963040002451231197248520341702226) * 10 ^ 70 +
        6132448149140326590978726464964597438240829867106021519416057346695077) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_60 :
    recurrence5Scalar1Left.coeff 60 =
      ((((5225047977940936006547325765080420533221494752050937149 * 10 ^ 70 +
        1723554330986892598528001890259533425411141211786651496812969149045574) * 10 ^ 70 +
        5705098302519570207180457217098230057926574760325040911805987684937818) * 10 ^ 70 +
        1247776186894525401277054371899378453834135036946053167907296815060860) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_61 :
    recurrence5Scalar1Left.coeff 61 =
      -((((169349709329438900655278210389992505964431358975952001570 * 10 ^ 70 +
        2219415974015133613781029153667112647999517790630278602928617355185946) * 10 ^ 70 +
        8139721911286847127875855365250961171854770698448827015427085560676962) * 10 ^ 70 +
        7335632042710817122131405762224759372527697174807219390526933266080660) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_62 :
    recurrence5Scalar1Left.coeff 62 =
      ((((5211067807247970583873125463857521551550814595181821338129 * 10 ^ 70 +
        9004606399776856804038769262940167839927336992941522315739701848474848) * 10 ^ 70 +
        5008720555654120303586042621395313702124506041631573819488658695625178) * 10 ^ 70 +
        9688030540721660088962344226582977166940224457318747921587225224433137) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_63 :
    recurrence5Scalar1Left.coeff 63 =
      -((((152241133167861809659724382012444487392009289645002650365313 * 10 ^ 70 +
        1442860456059842635052183080497671802740840642096092544686783530292762) * 10 ^ 70 +
        8750894018828002278273659370864778442775197841196415728224915538293486) * 10 ^ 70 +
        1678253819514596907750713771335200816682785729139225422729467551437072) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_64 :
    recurrence5Scalar1Left.coeff 64 =
      ((((4221849349808255800929723874025202969855242734689188500698254 * 10 ^ 70 +
        3127208764674441726766798605005938953081355467793032043673124231061757) * 10 ^ 70 +
        0430755612280543322788397983289026781827595425751376590230739808069314) * 10 ^ 70 +
        0878067649122148103487718757604583908603591427573409942230712697784676) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_65 :
    recurrence5Scalar1Left.coeff 65 =
      -((((111069293479876444154766445396994470302945089710960474171501894 * 10 ^ 70 +
        8838947984293307546028819105478486165117792909584374511712020523415003) * 10 ^ 70 +
        2302430989072389814446061401388448896038882111413858583181021676523456) * 10 ^ 70 +
        9903242669063666714956617013075511624324702697690092282478232500232776) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_66 :
    recurrence5Scalar1Left.coeff 66 =
      ((((2769230684819782295778453743780128929170149914390692259744782925 * 10 ^ 70 +
        8722872825989145016697201790399810701334771534464129865098699326338853) * 10 ^ 70 +
        8897321293563348835454881826681644705239381750285752965665082610705809) * 10 ^ 70 +
        9832266156839668928559268005392057867758104454729504866995253958440642) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_67 :
    recurrence5Scalar1Left.coeff 67 =
      -((((65322311607999522257015102071874887802535320955150052650327850868 * 10 ^ 70 +
        7929931348309858620952482726576561009321133603039685962755523377892953) * 10 ^ 70 +
        9253652327543790759233753392398475907012245667306604110682444814779128) * 10 ^ 70 +
        1411982482412362844547698409561670937043881963826160645431471139356983) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_68 :
    recurrence5Scalar1Left.coeff 68 =
      ((((1453871931675380830667610598637699113569411749761514773647468085241 * 10 ^ 70 +
        5004021470911368141535027780184315035685867439755413655440997248380836) * 10 ^ 70 +
        0722271252267402309531552272705501481945285110555294765758701775918185) * 10 ^ 70 +
        6802146597643124006428186660322854113576770095703950681289619957246325) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_69 :
    recurrence5Scalar1Left.coeff 69 =
      -((((30399971393152959913809206974107283082093948098939095627684542202164 * 10 ^ 70 +
        8482874319723034804453653553460446472629219254443631178804631560612906) * 10 ^ 70 +
        7440510176603449341495517843919875426970858109438186156354174232942257) * 10 ^ 70 +
        8957146593134171280961391744179823021027426380800383094912837381316816) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_70 :
    recurrence5Scalar1Left.coeff 70 =
      ((((592929641172971209693047082685843981553255486760194060951411557077354 * 10 ^ 70 +
        0281574671932247658806624169336779512317973996744084595557184051118917) * 10 ^ 70 +
        6761145547547418618491245944295565950142131726282929981181516588051519) * 10 ^ 70 +
        0021286628117129168169428335353362093329476792733685202278774282797802) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_71 :
    recurrence5Scalar1Left.coeff 71 =
      -(((((1 * 10 ^ 70 +
        0653452611440114480188164037109944574465159136706146152337405938592283) * 10 ^ 70 +
        6766319244308503095547107253649931959808541182987506809449869525662642) * 10 ^ 70 +
        4437020297507868367760961523306366174615136142504209461774790396424029) * 10 ^ 70 +
        2779523654114637605280295672685760450426664139249260998279613186487030) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_72 :
    recurrence5Scalar1Left.coeff 72 =
      (((((17 * 10 ^ 70 +
        2115806372968032736656025948022124977050588952329037329645723437243701) * 10 ^ 70 +
        8537039680307297902653397185563775427616061708313245756130810959681143) * 10 ^ 70 +
        2358464634682605184342032652223806968214824396459775031203788639301888) * 10 ^ 70 +
        7427819236582479069926251110102863374779468401572479928188585224044729) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_73 :
    recurrence5Scalar1Left.coeff 73 =
      -(((((236 * 10 ^ 70 +
        4170363997478260546513690537825560458129585043995124258158218336729670) * 10 ^ 70 +
        0713903532947013635385807813022640667257470969727429476907476729676520) * 10 ^ 70 +
        1870739515755853294090080397912014999794189468805722019563812481823722) * 10 ^ 70 +
        0193889205902073314254167558676337502313014880342570572961459018206481) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_74 :
    recurrence5Scalar1Left.coeff 74 =
      (((((2291 * 10 ^ 70 +
        3910732714957148961780694379663311844231446937500324179080591122417429) * 10 ^ 70 +
        7739735394131764231049854334272302849887487119466041215177863184279789) * 10 ^ 70 +
        7672887990784411393017012518016826322945999616006935112798391013970582) * 10 ^ 70 +
        6012951213903249089491930036260701693410108059963619894031226853647019) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_75 :
    recurrence5Scalar1Left.coeff 75 =
      (((((3017 * 10 ^ 70 +
        6425349896099127546826217084447429221776386901190258334783426055877696) * 10 ^ 70 +
        6084657672853625491094109932084136558500566448437467055655371212250179) * 10 ^ 70 +
        6351889721696387888693411340160525353955511234650264424781738860102998) * 10 ^ 70 +
        7906270607747798021012955480056487710969339649026883113298518377120193) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_76 :
    recurrence5Scalar1Left.coeff 76 =
      -(((((934554 * 10 ^ 70 +
        6289065950546705673674851873741692549970464190563416096183542114399118) * 10 ^ 70 +
        8453722033636098335111577879597313727173706053133541324486769990844673) * 10 ^ 70 +
        7216390832452600673497143548010487310816227355218957404656079870950288) * 10 ^ 70 +
        2122772778990639312768529844900833062844523545935636063023145551791413) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_77 :
    recurrence5Scalar1Left.coeff 77 =
      (((((32492598 * 10 ^ 70 +
        6149594036084159890416025556135957522991899992752306429625545183626702) * 10 ^ 70 +
        4425031238940903449227313485752653545039988184312452516435327999431366) * 10 ^ 70 +
        4845627629067650478584765847629245646182771972742616862738312423480792) * 10 ^ 70 +
        7188335164720960917454639669485272363379044791270208270195180097432031) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_78 :
    recurrence5Scalar1Left.coeff 78 =
      -(((((833669724 * 10 ^ 70 +
        9190768471022355750584871975687004527468187221635792337813541661517845) * 10 ^ 70 +
        6889499037267009480382677692257172044217692296014578328311731339256442) * 10 ^ 70 +
        6580211288229424805414296113821432565989550571836802106867038112814640) * 10 ^ 70 +
        0054738721759555633049319399782380413403434147839251672439540082271877) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_79 :
    recurrence5Scalar1Left.coeff 79 =
      (((((18438819119 * 10 ^ 70 +
        9376648313261837576916761839313564373281559830157820472238237152314611) * 10 ^ 70 +
        2965132892021772725684419053630076827523414860261619537787856319045220) * 10 ^ 70 +
        8963673774929728337905437255993365353489823708857845755488812736968339) * 10 ^ 70 +
        0802181855578126171156684417460364359796344119957619901817297391480015) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_80 :
    recurrence5Scalar1Left.coeff 80 =
      -(((((369828556052 * 10 ^ 70 +
        6359386389632025457525440947311973351881596339246664963394906115169090) * 10 ^ 70 +
        3076327151076051264668252899969674562660784848959503670969465210038464) * 10 ^ 70 +
        1399237672105090675324777637057882609637919427695630209043882604150771) * 10 ^ 70 +
        5950012391093390863214824558767472585055898091466609668920073121753220) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_81 :
    recurrence5Scalar1Left.coeff 81 =
      (((((6884128240039 * 10 ^ 70 +
        0797149881088998278908128857509745330709468415579417699710760637509528) * 10 ^ 70 +
        4191125827495342966135822305138744221743837119307936333716008986236226) * 10 ^ 70 +
        8114892914173321207868281232655093332245394736561313728954882597930062) * 10 ^ 70 +
        0434936721484503995327863102159634528527371610080651683338850609457701) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_82 :
    recurrence5Scalar1Left.coeff 82 =
      -(((((120441433072123 * 10 ^ 70 +
        9905726223848722004055114145957769171489781400679294539829896138961977) * 10 ^ 70 +
        2893761769911123724796113644335660492994030501225219172627155062132060) * 10 ^ 70 +
        5400549623332699045120229261604103433090123214000578083664221315483254) * 10 ^ 70 +
        4452164994794769591477237978641062826654749638964900739961283539798582) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_83 :
    recurrence5Scalar1Left.coeff 83 =
      (((((1995975769507973 * 10 ^ 70 +
        7307272392673431779993206013658893801238251014107983847707910416668860) * 10 ^ 70 +
        0172433971238641102522154233254619335107423921057068077285453783190421) * 10 ^ 70 +
        5716855599067799477056245884389125666586910258933238061139394550652636) * 10 ^ 70 +
        9243195105564427237402146703152477089415867030436462855051719135386314) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_84 :
    recurrence5Scalar1Left.coeff 84 =
      -(((((31494518313011337 * 10 ^ 70 +
        9319597612223059463701230352310862176462626860929630448973388848146476) * 10 ^ 70 +
        3177214303455992178961069880654087611386587495231583404956841119056364) * 10 ^ 70 +
        7267693778139915723338365780402806137746400700306719476770698774109397) * 10 ^ 70 +
        8048566731368646196418246755588576425503023962893099175480479741429545) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_85 :
    recurrence5Scalar1Left.coeff 85 =
      (((((474907423653303520 * 10 ^ 70 +
        9454057457180338274084959666028718199268661080507511023707375581525444) * 10 ^ 70 +
        5901703012896518390087492672379201697539533947695648015927789587315975) * 10 ^ 70 +
        5407900936414870862405510207230746017116750020561744817127139567344274) * 10 ^ 70 +
        7189067542372058493486095475074858132616540430300534384976367447721628) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_86 :
    recurrence5Scalar1Left.coeff 86 =
      -(((((6862215882538499669 * 10 ^ 70 +
        5292312653636286656140781450873798633618586900680783065969271838957079) * 10 ^ 70 +
        2691165316057702611924049316946366215639146103199172418593450448820316) * 10 ^ 70 +
        2451889264750980955832902309551442033306468439459085838026968170711394) * 10 ^ 70 +
        1503335933918407787752768424891290758552598875120980534275948855387351) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_87 :
    recurrence5Scalar1Left.coeff 87 =
      (((((95218531596786895216 * 10 ^ 70 +
        0786814856319311013022512775386047354464935103004255350707022203528929) * 10 ^ 70 +
        3693905497688111019568767093147381307742650599586018986600108574270011) * 10 ^ 70 +
        0929661378981618238369297808186582406714334495503578659380257241243843) * 10 ^ 70 +
        9185485183107929353057806363787624424613987017930652030593921316791409) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_88 :
    recurrence5Scalar1Left.coeff 88 =
      -(((((1270918414539887881823 * 10 ^ 70 +
        9209623838057775583370012905103918647252490972730736658238230817158729) * 10 ^ 70 +
        7306059741646003945551101970753794671213508156115200040445709105974088) * 10 ^ 70 +
        5247599009717765836796593530742241048641525655630241007638090017429211) * 10 ^ 70 +
        0900129485626805580378739145093150440968248729427912370258921950997738) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_89 :
    recurrence5Scalar1Left.coeff 89 =
      (((((16340318316422497564258 * 10 ^ 70 +
        2845604850975702761602492060375753974628723301853231928821885775831584) * 10 ^ 70 +
        4479598967337581327811180289110904646739602167598451810759259621776176) * 10 ^ 70 +
        6826862399242456166930502457260396507263072638748321047576824472756701) * 10 ^ 70 +
        4507781645475558681497944486244627414317832469287583636894147729728451) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_90 :
    recurrence5Scalar1Left.coeff 90 =
      -(((((202610760203990237436639 * 10 ^ 70 +
        4940593390135027129948271732419295086110703634488770890464857916150864) * 10 ^ 70 +
        4324548389553067669252858669448933803276242682879837550454473757159683) * 10 ^ 70 +
        1251505808775049620875887413254756316162694384009090941601818040209191) * 10 ^ 70 +
        6005066068560409430503037187286061342587723430232529404538660014289960) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_91 :
    recurrence5Scalar1Left.coeff 91 =
      (((((2425295877369027007595872 * 10 ^ 70 +
        7953389707071343059581551889751180668366891213387903437710222641889583) * 10 ^ 70 +
        4505543093295736717989622860131260202060533265368508233971467251189131) * 10 ^ 70 +
        8521244287239191949226847089819455306103199590989667673065412537679499) * 10 ^ 70 +
        4251480759260999889356296545996138457958373307591086308354048758691028) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_92 :
    recurrence5Scalar1Left.coeff 92 =
      -(((((28051321904694607365787608 * 10 ^ 70 +
        9085770915309548163172186837688691849671253517286589042986599525247641) * 10 ^ 70 +
        2157465002989958484658129544549864395917642948816605569269071714788971) * 10 ^ 70 +
        5092572005305185042721167971000674091099147979314430213670600604604219) * 10 ^ 70 +
        5347438144355295021923876098807121353920512400397993183334299670356675) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_93 :
    recurrence5Scalar1Left.coeff 93 =
      (((((313741067096397553658635452 * 10 ^ 70 +
        9350362614430659435868061936827051980201817545343510560328186537635701) * 10 ^ 70 +
        0824180080940945276222876331977081462793374600731817115254171378121354) * 10 ^ 70 +
        5107172530564353712565413698794707418771750152361670840707429801304500) * 10 ^ 70 +
        8312232346191939929438358447664917278390534588142355247007068898348304) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_94 :
    recurrence5Scalar1Left.coeff 94 =
      -(((((3395685434994574243557701819 * 10 ^ 70 +
        8539631468602711172072933484535165176527001341620723744709922596819653) * 10 ^ 70 +
        3198316757160194135806517135636887823410430170367677231011995863688734) * 10 ^ 70 +
        7715852838331982162551410026843253706424957638941362147399258204377210) * 10 ^ 70 +
        7719316856305094305367013955177995189130780366571846434973825638837230) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_95 :
    recurrence5Scalar1Left.coeff 95 =
      (((((35587887646394048837877311195 * 10 ^ 70 +
        1719271585514206642904968389260288291274559693262588496592335065309992) * 10 ^ 70 +
        6662007350814931398174456186379870662148599287625997476009958002764038) * 10 ^ 70 +
        9073939441914954131412138911802629099706360865773387592983535459465959) * 10 ^ 70 +
        0646394505551561227126752327181814944930954692918917316874310984549733) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_96 :
    recurrence5Scalar1Left.coeff 96 =
      -(((((361370922216648746447133854039 * 10 ^ 70 +
        1198381343583770479562378637004416581557632880862181548650180060816407) * 10 ^ 70 +
        6616770295900801986489269997714965629103376291630148280351646779934427) * 10 ^ 70 +
        0641298164857670149615735434236760784426367623395821656442623373295837) * 10 ^ 70 +
        9592607778725169574437625221580216111321933235438600739098955924197594) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_97 :
    recurrence5Scalar1Left.coeff 97 =
      (((((3557285312975617484758018711022 * 10 ^ 70 +
        0951918780511969722679372641655468207279155788201023031147315245814223) * 10 ^ 70 +
        8257035857228422339464521369771504562989528972466996504746674006619601) * 10 ^ 70 +
        6180607257989071050696725449001689161856587404056652056894819766691059) * 10 ^ 70 +
        1398874988782590344085480471852860478723152844319851033554452891011197) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_98 :
    recurrence5Scalar1Left.coeff 98 =
      -(((((33964140792787174666392391918582 * 10 ^ 70 +
        6289418117930730139326853816133462717934093225208744422299125744032862) * 10 ^ 70 +
        4401451449963607156926125961261939033715572218882644823361116709323359) * 10 ^ 70 +
        7710621174845698109517686975175723740345261710589310139410931388325885) * 10 ^ 70 +
        9815763848500939680147121214930633461405302265081695481760390909439888) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_99 :
    recurrence5Scalar1Left.coeff 99 =
      (((((314678412619655541767692219809019 * 10 ^ 70 +
        3908303765696819813200231440526971162478314904027414633834437956662809) * 10 ^ 70 +
        8952349429576932266162692580651824930602148205651708387387791468997074) * 10 ^ 70 +
        8207757145886320891426130739982179296489821379489899283162168218738727) * 10 ^ 70 +
        3062226381139052105817549264537951737816064603091188906386900537854339) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_100 :
    recurrence5Scalar1Left.coeff 100 =
      -(((((2830436974725472991987016514489086 * 10 ^ 70 +
        3907536224350514375844008745410037232137028950697368791198593546849266) * 10 ^ 70 +
        1197039386644742960848394288584852179295623843620540325948786936138456) * 10 ^ 70 +
        6459317461280940792499606250762733069155585297154176237933210775847779) * 10 ^ 70 +
        7790533415769053932627929869270900354235858369671804367009509794353224) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_101 :
    recurrence5Scalar1Left.coeff 101 =
      (((((24726661861241066038542243880427302 * 10 ^ 70 +
        3004057719366055304341797116119911347776217513333546027484615759385292) * 10 ^ 70 +
        2212043717898614075734318992208932365344462875682289375853381239349386) * 10 ^ 70 +
        1591863368777704261247756823915894840359414555177183836829555365569594) * 10 ^ 70 +
        1886411343602167115211872174081799521948168682756050048759609990816725) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_102 :
    recurrence5Scalar1Left.coeff 102 =
      -(((((209883765520524979316936944397163390 * 10 ^ 70 +
        1985470020761472490228579745466937636315439652557675972420663661829807) * 10 ^ 70 +
        3401751981481750651304364984175664896155157186357990973340397269690031) * 10 ^ 70 +
        4364037609922497443728102201914926108861926933216270495046859006886903) * 10 ^ 70 +
        7403656665431250643240550957737060267156603766439585582993638549420949) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_103 :
    recurrence5Scalar1Left.coeff 103 =
      (((((1731654043673431435760826803505657364 * 10 ^ 70 +
        0161403966320634385235235440926123720359868799842426348433742546621248) * 10 ^ 70 +
        1353186823581184904163405620155294526365291857556210352884037524314227) * 10 ^ 70 +
        7373512094625517685692062745461067046475227225306521580146494127281892) * 10 ^ 70 +
        8572883099625808790218959169222663563293721736912314702839825775738001) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_104 :
    recurrence5Scalar1Left.coeff 104 =
      -(((((13892245295145770288241548319869637832 * 10 ^ 70 +
        5994451111488042761268749687324513325589169332738451571098066106842985) * 10 ^ 70 +
        2715236052833256056336068260696683777848922205842829776758601575164207) * 10 ^ 70 +
        1578427922450325800562100089617310871724724842287071009279227159343414) * 10 ^ 70 +
        1597469822651298755190900012260911227121283970448241917153294418906639) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_105 :
    recurrence5Scalar1Left.coeff 105 =
      (((((108409197655182449996513089308565399420 * 10 ^ 70 +
        4234602968902509164147014566420350249540359080367154118479799279391282) * 10 ^ 70 +
        5321379450479424796908310704380624513252336982850706390775813248653049) * 10 ^ 70 +
        2753492208937700902820349709202758502627152077793147161566559622325157) * 10 ^ 70 +
        6600275239741806719745927357913486705442402402685036408642634461260561) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_106 :
    recurrence5Scalar1Left.coeff 106 =
      -(((((823169733020287156597711057668532981573 * 10 ^ 70 +
        4375076972934874203914053184403328253408753429407094427152244459863513) * 10 ^ 70 +
        4236698282195948950871447129578111584877169205421801191948943229568217) * 10 ^ 70 +
        3757596896555492826258418449879606405424962444303615974985701864078433) * 10 ^ 70 +
        1366995341724210838195214961841086509630952276445687984651351308938607) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_107 :
    recurrence5Scalar1Left.coeff 107 =
      (((((6083924310938660436007301902270578654753 * 10 ^ 70 +
        0410570449484902829867253628187355439804382900489262999193147625645200) * 10 ^ 70 +
        6931434597472380389624847492658552485974637621636495967449139367266637) * 10 ^ 70 +
        1284203538684370518610454828446681028303971377522758275241936152101898) * 10 ^ 70 +
        0140476652283793776995602397885768927318059828675031516733282539851833) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_108 :
    recurrence5Scalar1Left.coeff 108 =
      -(((((43781006019557426980776134033951005862087 * 10 ^ 70 +
        1097378325897938540641359968786116379085583008201272828930716218525227) * 10 ^ 70 +
        2352152264070254317892702317718520673940829453110895020167065226094559) * 10 ^ 70 +
        8627797102426127069314775653677031525500662099939914542423656412750334) * 10 ^ 70 +
        3918517703700784459553956183659409358642243596686856337350924078508113) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_109 :
    recurrence5Scalar1Left.coeff 109 =
      (((((306850452798320449209189622652658633949118 * 10 ^ 70 +
        2247993880178202616240714073348708244362972167703961021569252361350413) * 10 ^ 70 +
        2254659733585045737227677620070806345878808750897622930367273798078359) * 10 ^ 70 +
        8724092609875956112235832129184615663511263578171605432844144089954670) * 10 ^ 70 +
        1522195732923551859333502103423318159313157990778855036281443350741171) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_110 :
    recurrence5Scalar1Left.coeff 110 =
      -(((((2095241041946197737511570111658183420108665 * 10 ^ 70 +
        0309021490500283268305854270788746134647577749300339135418858379107890) * 10 ^ 70 +
        1752110058895067937335955193165975369531499760032367019012566793692636) * 10 ^ 70 +
        7765247075680390432405857931295317129461515913282881138647681063889448) * 10 ^ 70 +
        6242253600476423650744012446562298280708200854177677811635985949458298) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_111 :
    recurrence5Scalar1Left.coeff 111 =
      (((((13942168137126326070552544952432861040845036 * 10 ^ 70 +
        3559782672928872145519590819399805241515924240997916021440279717625669) * 10 ^ 70 +
        8244792133204631028353900496250225445490194701065599941264335007967267) * 10 ^ 70 +
        0387335960559085791784005318218733975071526983670079546493787631663856) * 10 ^ 70 +
        2366574047462217393810474200851149880029473615056289565603373445611117) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_112 :
    recurrence5Scalar1Left.coeff 112 =
      -(((((90434618540822392598974856745996858417926091 * 10 ^ 70 +
        1953885187769902138044713721169973189839293165595595323327485109187944) * 10 ^ 70 +
        8964295632890606702607056498956037291631727489230816323929926393900093) * 10 ^ 70 +
        9654385637845048405411558501519743936794785986386392034138931118480194) * 10 ^ 70 +
        0426824530935085626976744930107174920591984901774058903928027442209948) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_113 :
    recurrence5Scalar1Left.coeff 113 =
      (((((571955763095718681289508009162868346054867267 * 10 ^ 70 +
        9694872032141766771729830888478400890233958702904898296830099277991042) * 10 ^ 70 +
        9874899405501282494369968027585489825328647110942618294071808859735120) * 10 ^ 70 +
        4724754434232924554147961336127155390359405157948645280078657242432200) * 10 ^ 70 +
        7785158218777942161484992340534722142204111713640629266135927363915160) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_114 :
    recurrence5Scalar1Left.coeff 114 =
      -(((((3527973013726986462382328183712486402522913442 * 10 ^ 70 +
        2945597752164304635661841696956638985261327073009571562299061746449885) * 10 ^ 70 +
        8075561194032833578889333970424859334117994325730471095706429473133371) * 10 ^ 70 +
        8951041176780198057447051375518007306523244267730545321084417313854048) * 10 ^ 70 +
        9554283846300825164398011684263929120206146057270120763966683565321471) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_115 :
    recurrence5Scalar1Left.coeff 115 =
      (((((21229099359812947557914681527450471696208119331 * 10 ^ 70 +
        5809903244092601523697860657663359208229463790921314153715155637846404) * 10 ^ 70 +
        2664711875670404371847948104267614644464920718876756381409698733369010) * 10 ^ 70 +
        1156408686235553065329893879721966872275672108145712768043874429896237) * 10 ^ 70 +
        0921436981566777203382891381892251646488094519547839767739179988439886) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_116 :
    recurrence5Scalar1Left.coeff 116 =
      -(((((124648376721657355756642792040412395628265043624 * 10 ^ 70 +
        7461169392715613719356080940514478784771142971453016357545996402420317) * 10 ^ 70 +
        5532041418951741397358671610896983275857237063743292866683416582266371) * 10 ^ 70 +
        3244847823823763191695477132947310256062735852764730471079346031294983) * 10 ^ 70 +
        2364103193877311651966889545037379897128536880870758255823911518537910) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_117 :
    recurrence5Scalar1Left.coeff 117 =
      (((((714319713236538072628544382191250417290888270580 * 10 ^ 70 +
        5979521412903624359664605492486959774893027169212543163185075009323429) * 10 ^ 70 +
        2517421994235235415286822638852989975228684806702045774943485076235607) * 10 ^ 70 +
        2321089475303085210297574802513652310404139591991365248701011295175388) * 10 ^ 70 +
        3730644440988202387430379492063964371015151597006166801290286160672700) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_118 :
    recurrence5Scalar1Left.coeff 118 =
      -(((((3996215515288252391391766066317328152038117876917 * 10 ^ 70 +
        3040101972734767382918081911416988398007266089892003939576351427162591) * 10 ^ 70 +
        5099779778596615394283303385777118769586105401736933717810829592133905) * 10 ^ 70 +
        7664743506686028473606768884928399081137880876337967871753350626413013) * 10 ^ 70 +
        7151209936575972563212927136089295779142112027528505118744676595881403) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_119 :
    recurrence5Scalar1Left.coeff 119 =
      (((((21829910096104543647209711593244958497031709208330 * 10 ^ 70 +
        9421979959496315182540486770882301462925897342085550135599938582412672) * 10 ^ 70 +
        6898461755623046916082416593051666758095172469449839195502411464556967) * 10 ^ 70 +
        1239323363522047264790131945559679857621838074931470835235849107469387) * 10 ^ 70 +
        7573082067457637345018445193086991126789973858264865514449695484835706) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_120 :
    recurrence5Scalar1Left.coeff 120 =
      -(((((116465049989450759702926081850481661601264716666998 * 10 ^ 70 +
        5971490510412061743234546940692345569061070728080120906293441282508569) * 10 ^ 70 +
        0552075883420662527662870187826001483879909208379725578517019472126835) * 10 ^ 70 +
        1589763047817784384460423807357062033090726836299198145303277950847440) * 10 ^ 70 +
        1048958548451429061201479078692572276321611812836388766416037458285291) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_121 :
    recurrence5Scalar1Left.coeff 121 =
      (((((606975526115035216450812145593228894791036646590688 * 10 ^ 70 +
        8942449179037640996746395023874280094420609441814455070889331634578441) * 10 ^ 70 +
        7126994657480075693796923587626701735844597505030934127265941778290378) * 10 ^ 70 +
        6329837136706497035401249478241971067030923132254320434951619239192949) * 10 ^ 70 +
        0306549877974144110139904618680087914615958860151431831990698201555564) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_122 :
    recurrence5Scalar1Left.coeff 122 =
      -(((((3090775185897463830653746791894648490404698695736136 * 10 ^ 70 +
        4492625927871410772553057003648792404287740757609235406041000907994409) * 10 ^ 70 +
        8107365525550363756514222864203035006994584420685231598730674300318689) * 10 ^ 70 +
        2752033527397885755747979491181974559423552272136895642187090838660000) * 10 ^ 70 +
        3785858714373232200427881579476756235372228135116843652135137494292178) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_123 :
    recurrence5Scalar1Left.coeff 123 =
      (((((15380508963024516214963699895626264328501252186679621 * 10 ^ 70 +
        1081059086927929673527669558356956188765314445159749257902577225224260) * 10 ^ 70 +
        1905587476109214002090680937782623446960051396497955640794003358460530) * 10 ^ 70 +
        6925672783589503845166832978486347799195286665558481101521318462140999) * 10 ^ 70 +
        8037660868129092186020250969857189896707189435778606916009942766339463) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_124 :
    recurrence5Scalar1Left.coeff 124 =
      -(((((74810939331195414248332957757716934688907127298750040 * 10 ^ 70 +
        2724962951027899935059392287091521374188209700947311591537152047744729) * 10 ^ 70 +
        8016714437411573677785943957030125483829040913070073848645693554049972) * 10 ^ 70 +
        4659451417803062960625354043168905219768107975075262144675177165039341) * 10 ^ 70 +
        9020503254409683311241699647503675626910617971870901200275366867866034) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_125 :
    recurrence5Scalar1Left.coeff 125 =
      (((((355739775368277432400773093284472018242503038737782960 * 10 ^ 70 +
        5425097889313928599956290546816889768123066328941072533008674956181320) * 10 ^ 70 +
        3885360460551734241072231763352671873070113731526746723676495155926316) * 10 ^ 70 +
        3809224922933943053909288724035948670797138393316838403602343900840617) * 10 ^ 70 +
        8415753413338598238101885566600976010439963885103401305544048398069222) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_126 :
    recurrence5Scalar1Left.coeff 126 =
      -(((((1654063927874992344540309629043530736429097716821057142 * 10 ^ 70 +
        7220497026060011500129949797340364008664124373257328063773409464704966) * 10 ^ 70 +
        3329878359121054779913924531804627800530193174182391318073183261819622) * 10 ^ 70 +
        5646498170400066111790559063779988070881383435860629956292680347987085) * 10 ^ 70 +
        5903116835670601763933507167560292116421717910121794962902062792724823) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_127 :
    recurrence5Scalar1Left.coeff 127 =
      (((((7521461076183188335199652103243019441033854082813591471 * 10 ^ 70 +
        3270072244720151866279128767242262613089052868873233688416425488853638) * 10 ^ 70 +
        6255670072999739764041098329977383997249377866248673025972962726222955) * 10 ^ 70 +
        9165903875717186700807626605969998050073119502080578846523744850718765) * 10 ^ 70 +
        6779353582419255871322863197300023302125140499460310326236974203795415) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_128 :
    recurrence5Scalar1Left.coeff 128 =
      -(((((33454739350267554475415876433141587847487058294670795812 * 10 ^ 70 +
        8378950069021923022079186965080775159559642368155758960432476481989440) * 10 ^ 70 +
        2169482372135754269000376688265660814815518449558310969695463888276348) * 10 ^ 70 +
        5428470575871195999168584262946541827075924720694865029591287096341984) * 10 ^ 70 +
        8391124623951563816491322239488021766870224171291133648354653730993123) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_129 :
    recurrence5Scalar1Left.coeff 129 =
      (((((145576766542402714546373614634658994902949137412992910615 * 10 ^ 70 +
        4295784246083192737596786075694633232262550099538951646561778439744189) * 10 ^ 70 +
        7638448618890342877376294173279269047422215191488516366109248139690603) * 10 ^ 70 +
        7672301984798380773129837239329810465669572106979218590460140051423013) * 10 ^ 70 +
        7257156987560988891410760682199215460230922531820108534447687985509965) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_130 :
    recurrence5Scalar1Left.coeff 130 =
      -(((((619836278159794830563871800171106115881608077749433616088 * 10 ^ 70 +
        7684817999657003006379018111010312788144483494389739727298052091775552) * 10 ^ 70 +
        6934451445923234188024317594604392715024354219699014732405756704720926) * 10 ^ 70 +
        4965381892797620548536318895163194856686318630983125671060336614987390) * 10 ^ 70 +
        8488324387226724181379200534984894260770233149833261976217445314566542) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_131 :
    recurrence5Scalar1Left.coeff 131 =
      (((((2582748128283868389266759715547900698368952782019481267867 * 10 ^ 70 +
        6842391898242780384503138194446227705357630127090596182129365127534397) * 10 ^ 70 +
        0192964416471407139028104437140653135087929928754271351534818631369959) * 10 ^ 70 +
        2878494757919906017748961358546199199395578774951933583508832549962071) * 10 ^ 70 +
        0137477927421554612834136257998909098981478303610476816169161035786413) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_132 :
    recurrence5Scalar1Left.coeff 132 =
      -(((((10533557334115519440710332509283093417124882163415045777913 * 10 ^ 70 +
        4027274241043154479432708179632179424904279260465150905518770841928643) * 10 ^ 70 +
        1421775620070454967721308064023745335852519747782991939150858864945251) * 10 ^ 70 +
        0721215767084575833028339128043569846551511988980492944247736731613656) * 10 ^ 70 +
        9300595031938936799818909218458601659343437496542553800669509852971119) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_133 :
    recurrence5Scalar1Left.coeff 133 =
      (((((42055425416229195764668756651906811821172697506834260013656 * 10 ^ 70 +
        3221006414793871712940376397895029144823525318292835370299326188829528) * 10 ^ 70 +
        4392299179513599541468534603421072028290986291262988680964812219935552) * 10 ^ 70 +
        1393611682001924743485554629873522333487292533684640165249989417270377) * 10 ^ 70 +
        1824055026412353025633203390055325021357765479703780533997785893923939) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_134 :
    recurrence5Scalar1Left.coeff 134 =
      -(((((164394480443811190233442658722486455728941136594649534614178 * 10 ^ 70 +
        7483454375310292153024000326323523913854930237431334744643419955481650) * 10 ^ 70 +
        8777156985343505656651318148419463798052535577361807810753248457172811) * 10 ^ 70 +
        1432777827239052888351978719371602741253559435139665923790332769812867) * 10 ^ 70 +
        1216049544961526576670510013221124569251184136854564951500864255363694) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_135 :
    recurrence5Scalar1Left.coeff 135 =
      (((((629264524806088109929672706496485465586157185976221119419168 * 10 ^ 70 +
        4765038310758223234500131014583056620845995762597327504970248372191949) * 10 ^ 70 +
        8452119314875390060449739895850368991395700558568413818268114504068492) * 10 ^ 70 +
        4446929823180069686308332936845149276540955676226436237349214061095742) * 10 ^ 70 +
        9952989026953151984499347617288928266268259862905779718660376742429533) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_136 :
    recurrence5Scalar1Left.coeff 136 =
      -(((((2358962358343483431896504229661045266405231604367427609058062 * 10 ^ 70 +
        1294197147674208027605082038353541179954741672773197831549718563978692) * 10 ^ 70 +
        8131730508326772374377231195654933988235460580696512340748452857650178) * 10 ^ 70 +
        0285240787050915133143959696984123810629777902971208994435076054575493) * 10 ^ 70 +
        2702929455301729208602504304405538364032113774246108340284582240369128) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_137 :
    recurrence5Scalar1Left.coeff 137 =
      (((((8661833669142734901316485634187093498471037882688034820817006 * 10 ^ 70 +
        4844473320162749597975933963699197609585464343317442583052743323895833) * 10 ^ 70 +
        4726670780000926164644522562297575384663592597298730957984175011274771) * 10 ^ 70 +
        6860152479885115673227691607424293397998680065041659311152520293376906) * 10 ^ 70 +
        8907323962391077633393595181724434897065466623756255617561634886840204) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_138 :
    recurrence5Scalar1Left.coeff 138 =
      -(((((31157133066833353075581156593979114803597624747985510475718684 * 10 ^ 70 +
        7549219960505242347866154362190569321995830662812147375506608671837234) * 10 ^ 70 +
        7750716138838074363787090544893581366197318123988812386670738132075858) * 10 ^ 70 +
        0027687180081060250132365828563708568553885171522441227471936278404431) * 10 ^ 70 +
        3943518307105096453127353893012391340728564504281012479980342787893730) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_139 :
    recurrence5Scalar1Left.coeff 139 =
      (((((109804511532403455076605656127376180779853043684396111189230024 * 10 ^ 70 +
        3924934803992636531696541785719429774220165277929385194584440453520209) * 10 ^ 70 +
        9996790690031959979497439031377782133350166013225932000285735417835320) * 10 ^ 70 +
        7960321660058845640382842530899958021534946719708799043988224714315742) * 10 ^ 70 +
        0507459027173135806349151862944559921064634570160430487353074884227617) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_140 :
    recurrence5Scalar1Left.coeff 140 =
      -(((((379186320458276688540464732902340049779193269295860174002294842 * 10 ^ 70 +
        8809989718610764598273487016498539375111849254012528393636933047514705) * 10 ^ 70 +
        6855474021715944411083419857065757107838960286797390482670956493280041) * 10 ^ 70 +
        8514467949575379649395338334811562933400386878855469622576113471481291) * 10 ^ 70 +
        8794220507851932655540282433449295958753001225810911303368090197892785) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_141 :
    recurrence5Scalar1Left.coeff 141 =
      (((((1283240930326423889233317852517069123421547017106398708404133897 * 10 ^ 70 +
        8230535809659521502595871016778666321360493866835915061565397304948825) * 10 ^ 70 +
        3946069567412043368495320328334961944832696226062897789372628648143301) * 10 ^ 70 +
        8560491080202592738168936845563238511243536918657536646935595476287268) * 10 ^ 70 +
        0380305725843955187413232375232760338573302650095083590043412032832766) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_142 :
    recurrence5Scalar1Left.coeff 142 =
      -(((((4256363179280986425920282274441150210524553445827593136410296307 * 10 ^ 70 +
        5680205476552452467935766702480022975444867526488014241881545382991974) * 10 ^ 70 +
        0698979070250444875149747951761766914766193630669818189631180974229353) * 10 ^ 70 +
        8579359807444497998300425703747938904898062447147588161525809110592685) * 10 ^ 70 +
        3025398633125722385032519716595076563909465209186615119419633429817661) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_143 :
    recurrence5Scalar1Left.coeff 143 =
      (((((13838676880813386568365312620441853844939675839697321932238357167 * 10 ^ 70 +
        3093376132446872791141394317321628202019367565619899875592098598883102) * 10 ^ 70 +
        8171268422145191174911948877798222142727332228634478116607244699405054) * 10 ^ 70 +
        1563571957230051826109074945831114678902525815787832082301129962361665) * 10 ^ 70 +
        1606309624539148424649138225040745290821333311653494937268984963843987) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_144 :
    recurrence5Scalar1Left.coeff 144 =
      -(((((44108776959580523064212098377518257050042716050015438410357336074 * 10 ^ 70 +
        7654677230230184448494298522537024118798692720920977538679879890267834) * 10 ^ 70 +
        2069048980814701516476362342067336972187012451724986868889847599805839) * 10 ^ 70 +
        7110651115881297364603069286684548690055796283288506853285930385948540) * 10 ^ 70 +
        8044390142789599785708293919634786390609891601839874100796069864492718) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_145 :
    recurrence5Scalar1Left.coeff 145 =
      (((((137840817776661508162988243655660213312580717965574630898255312828 * 10 ^ 70 +
        8055017330787591033752404332187635688767081955540345710917613259012596) * 10 ^ 70 +
        7967480966000928979619388096608573893584627510025759877603139883502123) * 10 ^ 70 +
        2038805756012894031371844716293352781575588482234934104587774332796163) * 10 ^ 70 +
        7664766892869405374578694470001952947509304545069570338366102580251770) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_146 :
    recurrence5Scalar1Left.coeff 146 =
      -(((((422376341811604124898634503803971174349281626747643888287612641169 * 10 ^ 70 +
        5526753748324774810416482496945133749267671705984834630415113983468474) * 10 ^ 70 +
        1278114995230946657203336682118182634584550852624838623752533307795794) * 10 ^ 70 +
        2960410491825923135499069158806402895211127523709635028478039203138319) * 10 ^ 70 +
        2342436757248896839447858547017311653019319674369927364171996644445733) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_147 :
    recurrence5Scalar1Left.coeff 147 =
      (((((1269215987282164157777271778096189212039563119674166035886260800110 * 10 ^ 70 +
        7054797002902330571301389147596973694414661280570495980900610934008459) * 10 ^ 70 +
        0670637913697247798293059923866179015670937531444825970637499813917978) * 10 ^ 70 +
        8411734928103174941528918145309920049776762657379605783111357747521101) * 10 ^ 70 +
        0947411661739485053823203283851575801155265067409434453585869390611997) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_148 :
    recurrence5Scalar1Left.coeff 148 =
      -(((((3740500820474360976151554001552529414013668631343997218193205295479 * 10 ^ 70 +
        8190948713993936288900182786391759530231055131808037919235829865039067) * 10 ^ 70 +
        6947238059638968209552864826452811062660350977932137765207271658200503) * 10 ^ 70 +
        5338681225164663571576783585783197636967892020024631331083452850880540) * 10 ^ 70 +
        1937476904291441232285472210669080174199355271922336583780513034811973) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_149 :
    recurrence5Scalar1Left.coeff 149 =
      (((((10812475004751850539642348958464014326502896575683149894988959642011 * 10 ^ 70 +
        9176030884406389131431003474376163184276556818003732008172350289493259) * 10 ^ 70 +
        6141985742446436501407648458108247579576701657993232396518552759121152) * 10 ^ 70 +
        5728491833104011925033191162124900978920394651989969561117124079611348) * 10 ^ 70 +
        3127252701921986123210144027639781516177076212252692586158738607779331) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_150 :
    recurrence5Scalar1Left.coeff 150 =
      -(((((30659376916064230514067623902798637599699659736321748089908139409666 * 10 ^ 70 +
        4036139525628488546140683699574622667401386909945958410487339141508414) * 10 ^ 70 +
        5197202606806613902828754300592768073717704882882187383958574139030893) * 10 ^ 70 +
        5961903135362009019890669509650922444217585827356004109419237761781113) * 10 ^ 70 +
        3053695356126120372997968928807259144992238088779653987775636705463746) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_151 :
    recurrence5Scalar1Left.coeff 151 =
      (((((85287413187602865423668005165288285478738788995525740904196131274357 * 10 ^ 70 +
        4264365144679498091492357510700273272978731152482788936369273056320400) * 10 ^ 70 +
        0023829194138631865878259663408658554803566316157757354575059335600613) * 10 ^ 70 +
        3630025488983700424444164569269580188352023480092837625545527310409059) * 10 ^ 70 +
        5932571262227379847493745455260586701238060012981597402062442877622221) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_152 :
    recurrence5Scalar1Left.coeff 152 =
      -(((((232771292699691051027661358639878857586740279418125386269115129240226 * 10 ^ 70 +
        4795705159071663053903603909795837351468422300527659951853501018214129) * 10 ^ 70 +
        6885407420749797226286530235895311587973375792184595200030484460679258) * 10 ^ 70 +
        8838366113465440835299185557151139075704021205986186246561547114073569) * 10 ^ 70 +
        5165750116924181522161328434326053451427737948529328452603706854679451) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_153 :
    recurrence5Scalar1Left.coeff 153 =
      (((((623354517703126204978602253953472602208284961866955226508141158310641 * 10 ^ 70 +
        6499793479243096690755468452011147479723556333052161824881883656805716) * 10 ^ 70 +
        7563335302345262370488291670824652268409985146276297787035776502837616) * 10 ^ 70 +
        1380235367719530910719739713499177176364822021451847638780069072273138) * 10 ^ 70 +
        6235556740172030026029868734795311386656712519238485904600979647078187) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_154 :
    recurrence5Scalar1Left.coeff 154 =
      -(((((1638095854719201474149139298841170667136738651122954946083404070296745 * 10 ^ 70 +
        4108465873599913811497042546601535263539494941343438960374822986626427) * 10 ^ 70 +
        7740090620652359888595347694558046220832603990930886545181626738446588) * 10 ^ 70 +
        6422148610300002864976157833015376405579869152369157621183349884914950) * 10 ^ 70 +
        1288198052953840967318677274003888418903794282715515900051039771354624) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_155 :
    recurrence5Scalar1Left.coeff 155 =
      (((((4224528683271677953982320069647581952312531132999715084719624540437269 * 10 ^ 70 +
        7795628158438697341307023933314512333787748735064450317871473403000879) * 10 ^ 70 +
        9723486938359011102890384633965243380414782598108618424102809645493889) * 10 ^ 70 +
        5665585630129782281472447508370288405067254558216065276178504101275678) * 10 ^ 70 +
        0221801389524434122158528719417620863347714717428071662489431736610173) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_156 :
    recurrence5Scalar1Left.coeff 156 =
      -((((((1 * 10 ^ 70 +
        0692695190216115861727300138034053852760516586840529121075852688440867) * 10 ^ 70 +
        1922086447431601454744201609683113276768869177218322835696524213808225) * 10 ^ 70 +
        6933129116982337227030408738094937276067047257634435974364161492491331) * 10 ^ 70 +
        7972172378322094299557636354160416616849192817837326219779671156140042) * 10 ^ 70 +
        2060217258458344715689864159158328978274820915326961864468784048033214) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_157 :
    recurrence5Scalar1Left.coeff 157 =
      ((((((2 * 10 ^ 70 +
        6564417487005932959052680823831639191117452438864661909840030608096683) * 10 ^ 70 +
        1848560188352712003712858589660158586739541531362858205543106223164812) * 10 ^ 70 +
        5214907409745780426723167053156049069088565050681015213444185390308609) * 10 ^ 70 +
        2048181389512088857412871691987402530745196465930490219907844293249255) * 10 ^ 70 +
        6113023661716647766168322352015653003054850405532128547952467542436280) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_158 :
    recurrence5Scalar1Left.coeff 158 =
      -((((((6 * 10 ^ 70 +
        4781473426448542499540339301775731768803198800572587959989268065952729) * 10 ^ 70 +
        5384334258683887679650000464278961943842494952969568133605747656648893) * 10 ^ 70 +
        9319888167659992056131490120557245296655499372794193508239432322065859) * 10 ^ 70 +
        1237164878919391897472611270378166161300964375687793856617436977368355) * 10 ^ 70 +
        4821844940251872432508357738604161359672897243615593064540109729984922) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_159 :
    recurrence5Scalar1Left.coeff 159 =
      ((((((15 * 10 ^ 70 +
        5085437390052220541777008164685354195017804905182567470296746916323477) * 10 ^ 70 +
        5038537201144752057582825083027604834361001174146030553486302746474768) * 10 ^ 70 +
        5819433449511886060964747239320303494288441823173495120057241974954604) * 10 ^ 70 +
        3978508480488400036392119903664328930027623527147980197840238290774673) * 10 ^ 70 +
        0378234137787558377103706598505297951233503304619946295434610126012734) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_160 :
    recurrence5Scalar1Left.coeff 160 =
      -((((((36 * 10 ^ 70 +
        4495520119896607890026777768158390479301155724007380986817080513466359) * 10 ^ 70 +
        0246661520038510149196322244523745157346154842427003626010631995266851) * 10 ^ 70 +
        4785330880783474352582147482411970894428388984892167752685481636684512) * 10 ^ 70 +
        3303323910189531912865364680482124920523704078787500279139942795983266) * 10 ^ 70 +
        3517358910810033351302687398979487701091707154451218543460579432472288) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_161 :
    recurrence5Scalar1Left.coeff 161 =
      ((((((84 * 10 ^ 70 +
        1094349239863064045905814353353203142661209529782265831701320307570826) * 10 ^ 70 +
        2817768395662539702783563487517771699331530422786149660610396434070313) * 10 ^ 70 +
        1731783098441118580040662931926325444198330138209874180348481561305648) * 10 ^ 70 +
        7702832564224962327690882801199270802488051885768960106929826111687670) * 10 ^ 70 +
        0184777285900026372698285229978139444444219428332134112577540342609300) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_162 :
    recurrence5Scalar1Left.coeff 162 =
      -((((((190 * 10 ^ 70 +
        5715303978075747311835622168941094108060484689547595367582412980711560) * 10 ^ 70 +
        8895730169429562341661224558117167173010709580372676107297917782824146) * 10 ^ 70 +
        9326788090022128789518861556400473887257702947362121889708919658861204) * 10 ^ 70 +
        6119319979604804207654338326072348333274526017330039307104407032170126) * 10 ^ 70 +
        2600369119531410348198703374608613466801430837229218435690825177365605) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_163 :
    recurrence5Scalar1Left.coeff 163 =
      ((((((423 * 10 ^ 70 +
        9949096915369551762962684927619280600475084708247335245951901255100843) * 10 ^ 70 +
        9641582184841555037254438272409209216063078079547142469180171995120233) * 10 ^ 70 +
        6320051363556099318095985573822892380290595758416846691305384616188921) * 10 ^ 70 +
        8244667800292138607468484768629608634971047377815187486180881421533100) * 10 ^ 70 +
        0236900205453833623709934250808927167967386852349400819872812109819417) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_164 :
    recurrence5Scalar1Left.coeff 164 =
      -((((((926 * 10 ^ 70 +
        3608766401717460907993990459470234958359924866211073886682001450290942) * 10 ^ 70 +
        2880895281626939849305803383215467791756754155544654986124062310562021) * 10 ^ 70 +
        5478004326155703369199140099238583813043243918724978219678606729035357) * 10 ^ 70 +
        8050804267178587255898883708827750335218298193405396689449571077039480) * 10 ^ 70 +
        1028148717038277755043992438931273493064386096630025283384469562969511) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_165 :
    recurrence5Scalar1Left.coeff 165 =
      ((((((1987 * 10 ^ 70 +
        6661557334469863544980073439082915102392096461209805123076066680123834) * 10 ^ 70 +
        1629910467532855610932836718530480317022383818523233298455900422687154) * 10 ^ 70 +
        1962311437621753050366703475831616885788044663435201219127263523202829) * 10 ^ 70 +
        3468122011242625524992998712148653870745801744052023043517285312277375) * 10 ^ 70 +
        9005795789299505598101413668802100188166140373970318968342646660886376) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_166 :
    recurrence5Scalar1Left.coeff 166 =
      -((((((4188 * 10 ^ 70 +
        6705799568581678275384173865474851760249127494507898521336235245971989) * 10 ^ 70 +
        4455390405824250318772494136469818868687479085165520722605247926962586) * 10 ^ 70 +
        9094717517515578777846799256543455556477915208149742875751964922947413) * 10 ^ 70 +
        5922619783547374504004765017650474213680572072527915986932432660361141) * 10 ^ 70 +
        0556334781415320273205376513042821379612546177630420885316623834238205) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_167 :
    recurrence5Scalar1Left.coeff 167 =
      ((((((8669 * 10 ^ 70 +
        6879773860822389276825625431042117833653038182640914690359533095977363) * 10 ^ 70 +
        2977854886360423227383383161214784488248905230979821129698681921451699) * 10 ^ 70 +
        4458553481059905282192126009663656679593292668511577281092627353077958) * 10 ^ 70 +
        4720326273281556443311897487864810423560026326030861668469106928804732) * 10 ^ 70 +
        0229797499053473804012030927393427067159480167923434219140380821905170) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_168 :
    recurrence5Scalar1Left.coeff 168 =
      -((((((17625 * 10 ^ 70 +
        8198018667857599049314812032687246918642295655223267608920830415921240) * 10 ^ 70 +
        1438770314810411572848707979066303854897044268630144026865603919098762) * 10 ^ 70 +
        5200049506553273342630696716565267574072967719283182449901332030148603) * 10 ^ 70 +
        9945935411270919106383186756507763384221516470012082490460472959987214) * 10 ^ 70 +
        1551173355016286673934220341297407162281175618752895065535024595451788) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_169 :
    recurrence5Scalar1Left.coeff 169 =
      ((((((35199 * 10 ^ 70 +
        5419321100695076236844795584346091476891705176635104896012699587911407) * 10 ^ 70 +
        7042612289168975407703521388292599599932757905434005113759519302931523) * 10 ^ 70 +
        3085339278916872124920366669236315284840187885106932751664722595250545) * 10 ^ 70 +
        0983520773542499729265181553079655745027114619149573217713860406088331) * 10 ^ 70 +
        0496589385839929343065998367608926086097710787053842311089977050859614) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_170 :
    recurrence5Scalar1Left.coeff 170 =
      -((((((69054 * 10 ^ 70 +
        0077028988894621589208258538213067220947224469244537610171492961493468) * 10 ^ 70 +
        0912638698118734631626917446815753113732641839380132729999289559841770) * 10 ^ 70 +
        0205294330930850362745095796158459916542774270574111796613655728503710) * 10 ^ 70 +
        7993009531535119354859865461927056067747144716831910615404526849039180) * 10 ^ 70 +
        2275208249292071170580778519681752877471468094892057145796350828994755) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_171 :
    recurrence5Scalar1Left.coeff 171 =
      ((((((133084 * 10 ^ 70 +
        1861342703628448072533377007591867735306201657164629096134501774422300) * 10 ^ 70 +
        2997360128543972129416224324842514379394204229267970568855303053341619) * 10 ^ 70 +
        8136446403228446453436538178431593954604962747046642052722378157915921) * 10 ^ 70 +
        3254062744801557559505321206812778205128942483140929271225505020583830) * 10 ^ 70 +
        1936315250677076382076022635535539663983192667059988272081818496699661) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1Left_coeff_172 :
    recurrence5Scalar1Left.coeff 172 =
      -((((((251982 * 10 ^ 70 +
        4716461381519285340630467295866338738964066574257199722854333024096554) * 10 ^ 70 +
        1487568834836043529972450834205149864273990257901861378105256905239990) * 10 ^ 70 +
        8861631544438874945346064981873279258524785435980310616099537608400112) * 10 ^ 70 +
        7266801032954965080695275857468526449947522578704632700456101373116216) * 10 ^ 70 +
        5025756816709015113508998096393145927861691376447062563524594645088193) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 0 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_173 :
    recurrence5Scalar1Left.coeff 173 =
      ((((((468748 * 10 ^ 70 +
        9187024250402410032400852327176659807089460315345905533431192949820904) * 10 ^ 70 +
        6004249769411865529631080963776731011557247795178697428445380605242801) * 10 ^ 70 +
        5947799789034784528281625694994826900657692450449023944039597709329333) * 10 ^ 70 +
        3823097697015832131647243168829219443209033689881198259844497412215110) * 10 ^ 70 +
        3566739381786632477784167578504220373435502387477046902760738360148008) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 1 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_174 :
    recurrence5Scalar1Left.coeff 174 =
      -((((((856752 * 10 ^ 70 +
        0877331520314261581005894585696411973992550152564702783907841832725280) * 10 ^ 70 +
        2775338028856579573886554751813236091713834666322547896659072925813210) * 10 ^ 70 +
        7775767247201474929894527125265593550409712106272362093417227334127072) * 10 ^ 70 +
        6481266754584056988017156065191276818635346135446364784786245493059385) * 10 ^ 70 +
        3066976302316962514849173184039587085259229731226411902544288649065715) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 2 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_175 :
    recurrence5Scalar1Left.coeff 175 =
      ((((((1538625 * 10 ^ 70 +
        7579378827572267150672275933725660163977624919723291402730972624937688) * 10 ^ 70 +
        1078063328111625867667050881495097245909707413907491959535100527976329) * 10 ^ 70 +
        6985849276352307765346539493513905133249327832514672376386939517675244) * 10 ^ 70 +
        7267297045385744744367660273646549119552707620121610432789934645991960) * 10 ^ 70 +
        6635320097135026302769212359911956068650321199162803953855719753177126) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 3 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_176 :
    recurrence5Scalar1Left.coeff 176 =
      -((((((2715131 * 10 ^ 70 +
        4065208768284932264602367987076397689434571698325498048886922652036396) * 10 ^ 70 +
        0414686986990049854584631928446779595285603466342276145278706396837402) * 10 ^ 70 +
        2345593161870674348259897429935722982407069982557123677943594424875790) * 10 ^ 70 +
        9987202417514451923386630569185227247449166168427830051897000204430582) * 10 ^ 70 +
        2717781709887689699779940742559310153422216020187417820315630478818912) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 4 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_177 :
    recurrence5Scalar1Left.coeff 177 =
      ((((((4708091 * 10 ^ 70 +
        7558296627167218234345797120351210212223314749478774856161700688607916) * 10 ^ 70 +
        6777263454673447468252887191162541808864513495697607974145112649690880) * 10 ^ 70 +
        6667541870753712548248594814902212954696743867145368154412345262304527) * 10 ^ 70 +
        1376822919409845558971652767798511084125498831898336949948240746424127) * 10 ^ 70 +
        0420096140296308026749958228969198574725709122805287711667976716911225) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 5 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_178 :
    recurrence5Scalar1Left.coeff 178 =
      -((((((8022513 * 10 ^ 70 +
        3747873284231852252661729683540307471979103611783386537764340807025739) * 10 ^ 70 +
        4114531783357529284664579731298861505861856278524717493464394126279714) * 10 ^ 70 +
        7192742240012449611081916440794710864046971660024021434931548157069651) * 10 ^ 70 +
        6277591487071478179591800094440588654091621321521806718230228517129587) * 10 ^ 70 +
        3739787503568312351758785024105462421351448732717751481928169218160917) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 6 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_179 :
    recurrence5Scalar1Left.coeff 179 =
      ((((((13433889 * 10 ^ 70 +
        1277987386500101060029195309483666102829399624013896563757325887286449) * 10 ^ 70 +
        5603629302283927878275801365994339799581496218594195194326861597739897) * 10 ^ 70 +
        7338292888295378092148910023806859554699565053716451888478138961673141) * 10 ^ 70 +
        0626962047889974332996914583506904789637936092196054609560397687043301) * 10 ^ 70 +
        2181576662324010334624987819745287268913104745778214520946892613871756) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 7 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_180 :
    recurrence5Scalar1Left.coeff 180 =
      -((((((22107121 * 10 ^ 70 +
        1724876949610771781400963979308208241838445873426420014570843035566772) * 10 ^ 70 +
        1118665829160190158994225195445277079349132226828382247183689467876281) * 10 ^ 70 +
        7632142721526901866386561747049838246694526161628802181738034075257765) * 10 ^ 70 +
        2845473417836643420208164589652383444875199548704629441216806342116880) * 10 ^ 70 +
        8483771065689580016798887949474737878703680430626532448622844561485573) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 8 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_181 :
    recurrence5Scalar1Left.coeff 181 =
      ((((((35753132 * 10 ^ 70 +
        2856390691014048885120180342737277519433941868543136379748138476271000) * 10 ^ 70 +
        7549950354668809850032552403873321779368407359204646504622988040306575) * 10 ^ 70 +
        1225773018555075821747163129521750670898773131874433831032731237476601) * 10 ^ 70 +
        6160553654722848536736170513227386697450453889225426790801197402978862) * 10 ^ 70 +
        3842453181775400853844736493559635764448838187828952602188197232294459) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 9 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_182 :
    recurrence5Scalar1Left.coeff 182 =
      -((((((56827532 * 10 ^ 70 +
        2910358489019605128869472758975426159926683377034065608004240273607172) * 10 ^ 70 +
        6396653176063174275826283654488189221032660865173387738345267733514048) * 10 ^ 70 +
        2334938728639844363158975714434351394360527317093439081027917048815621) * 10 ^ 70 +
        7848674660137194590026657094704784179345798206759136967329445701887638) * 10 ^ 70 +
        2990027287886202703634435124319815241600139943824079070311194504051017) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 10 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_183 :
    recurrence5Scalar1Left.coeff 183 =
      ((((((88772114 * 10 ^ 70 +
        0254113531405526898483888107020778643367649958725616035938443372461790) * 10 ^ 70 +
        0658913422912560018518491956154136154980187478917781562823218744314992) * 10 ^ 70 +
        3189620637700155048723150951358051652666317038893857428335655133912118) * 10 ^ 70 +
        4904294137854972759598317488029003523874115583043546510825863794297032) * 10 ^ 70 +
        8275987639255310390696413121620440075917593667285316492092832271137228) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 11 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_184 :
    recurrence5Scalar1Left.coeff 184 =
      -((((((136293943 * 10 ^ 70 +
        0154770624916162156829209192738627710494090122437361648663684267786671) * 10 ^ 70 +
        1861768358039327488039442480384196297219678901079227821826456103294758) * 10 ^ 70 +
        8730421140372025052565957666096543335618248590884961932743260976666805) * 10 ^ 70 +
        8404299386605249568455562160878264503874313602149114838407451063623881) * 10 ^ 70 +
        4285690437914406108422267309924407831355329515935033852898598733788068) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 12 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_185 :
    recurrence5Scalar1Left.coeff 185 =
      ((((((205668034 * 10 ^ 70 +
        2006255512276024846169486667511888315455924121085770214638546768061485) * 10 ^ 70 +
        7305553031229588337087888629909415323523392153685027645934607082647814) * 10 ^ 70 +
        0538402264401918228351319217209113388475249987724744651509351089411223) * 10 ^ 70 +
        1083837577650655554649990413920884324310392599635240941925595707784096) * 10 ^ 70 +
        7464798208516172172080682791806280459164140150903790620859884273985722) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 13 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_186 :
    recurrence5Scalar1Left.coeff 186 =
      -((((((305038112 * 10 ^ 70 +
        0767328003233379098785603505419041762853418415868625223869066708873022) * 10 ^ 70 +
        3897183793715417823300166809613095693531094678784443650417730614189594) * 10 ^ 70 +
        9004594481211353678606820767421200972305890481394012867661033514073718) * 10 ^ 70 +
        8045256624735199607751412030472688027979424112167905408002786860435165) * 10 ^ 70 +
        3240224969297943788872349082752707304286994914332529546000915580744803) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 14 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_187 :
    recurrence5Scalar1Left.coeff 187 =
      ((((((444676353 * 10 ^ 70 +
        7124725726723107383688443403084084553126112801088603236050142324743725) * 10 ^ 70 +
        7081249215358736309638063451300334779259470306464595458167564508779741) * 10 ^ 70 +
        2296399787565970058093234214011580986885082183484641591734050841285327) * 10 ^ 70 +
        9163832424539419550446203677070201884255900294602667403027382227883310) * 10 ^ 70 +
        8481079568943620088740324753785989527231341757790456614813254193294412) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 15 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_188 :
    recurrence5Scalar1Left.coeff 188 =
      -((((((637148725 * 10 ^ 70 +
        8493460108042361083518973679573979624754909515903900091496468017650715) * 10 ^ 70 +
        4244074335109220500193241438709860834910719804490880331925037741367019) * 10 ^ 70 +
        4280660172490257839151900086220235523305310343541026735207235681920512) * 10 ^ 70 +
        1616551119841907259713449593677045031871670925955755212069221379970346) * 10 ^ 70 +
        8655022302182776059089193144936154615310106570123018823617677037224352) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 16 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_189 :
    recurrence5Scalar1Left.coeff 189 =
      ((((((897319841 * 10 ^ 70 +
        5915239012598532804836832464411758157356894580495910968382401817943471) * 10 ^ 70 +
        0356577370475946877391040081661244676594882775139394276010271350308333) * 10 ^ 70 +
        8889139989480951911175408856521518089466576080009795750644508487744221) * 10 ^ 70 +
        3675411408614051430367182165872371109108002392015346865881802238932028) * 10 ^ 70 +
        4497791541990165095200551887040521167359902556532539630454044851178854) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 17 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_190 :
    recurrence5Scalar1Left.coeff 190 =
      -((((((1242123298 * 10 ^ 70 +
        3927900552148069629291995828764241276768860887145737048936154578624524) * 10 ^ 70 +
        6351419433617223497594516530170706315372526146999192558805345352372482) * 10 ^ 70 +
        6267650149838643607732407115949147786577233868004609738127694068250821) * 10 ^ 70 +
        5805849653354306234228792976529527857051704917220867453263574793597074) * 10 ^ 70 +
        2086965967997511418816024828361378018525587761912643108381208068203961) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 18 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_191 :
    recurrence5Scalar1Left.coeff 191 =
      ((((((1690023872 * 10 ^ 70 +
        7212899545004262440742978333731366532128538649042627817966325191549636) * 10 ^ 70 +
        8264519048632565425202268003978736631952862911651874930320039904162182) * 10 ^ 70 +
        6027680684027130617233298223598933945772109403231537966190462686747416) * 10 ^ 70 +
        8424303957887263387677909745417927004358584110791225190164537060801785) * 10 ^ 70 +
        0622206141796152841236617263900525014521159721510176046043728742243748) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 19 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_192 :
    recurrence5Scalar1Left.coeff 192 =
      -((((((2260110374 * 10 ^ 70 +
        2378252854120503278660107603300860880930202059394640860449515309472801) * 10 ^ 70 +
        7361878293950574629576110317165702727320471401236872832854509600228341) * 10 ^ 70 +
        1367308112710959325924164125330419265304431388818481604053029054309536) * 10 ^ 70 +
        1896875546543103607310013362327302575132812973629681032681396467257109) * 10 ^ 70 +
        6230601635921635036853969940622497516685773417337658977360771447806708) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 20 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_193 :
    recurrence5Scalar1Left.coeff 193 =
      ((((((2970785218 * 10 ^ 70 +
        9958721733434232339443218813154970842480804192650266215862529918200782) * 10 ^ 70 +
        8006446947257157190212178833558795337017153582943699994587017092406573) * 10 ^ 70 +
        0555317638047378436665781862750646323826236232653216115389651977272100) * 10 ^ 70 +
        5845174925483012724289280838466781092221035716983336556761532341011777) * 10 ^ 70 +
        8287875598783038843072211690054107856355425037680808680395452636458418) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 21 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_194 :
    recurrence5Scalar1Left.coeff 194 =
      -((((((3838059910 * 10 ^ 70 +
        3031808923822866971124891715609948477642250870701863189885030375663416) * 10 ^ 70 +
        8210991754155336499821429399519277265230465131248519868938139959917416) * 10 ^ 70 +
        9645116098137510363533616295452135171743000385237774435616011334894672) * 10 ^ 70 +
        7520934703149013402152896508517970639935637231641740712388584817162875) * 10 ^ 70 +
        7452170252381825963092129223322374867280183945950331697660774849798693) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 22 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_195 :
    recurrence5Scalar1Left.coeff 195 =
      ((((((4873522965 * 10 ^ 70 +
        7259313961546992344960731376409399511806476338383039101255480103227203) * 10 ^ 70 +
        4240109290643811701818018162638632830264127164156658929101472414281030) * 10 ^ 70 +
        4424984207901516922689501547502274478919410241193300459648032755536070) * 10 ^ 70 +
        6855131121935380992991168823760454822930781896956272606203695901728657) * 10 ^ 70 +
        2167305623976856896307016634655158781219837360679754649495559187061635) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 23 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_196 :
    recurrence5Scalar1Left.coeff 196 =
      -((((((6082113400 * 10 ^ 70 +
        5736339350841993210994385234478108784592904118355303879583123728350794) * 10 ^ 70 +
        2618257651144835855376236984425242391093176284278379037494357626499947) * 10 ^ 70 +
        9384927749917024468298312143465041080847103746670287105741685984966353) * 10 ^ 70 +
        0501217738336475457862156999440256710708203164291810193522958994297178) * 10 ^ 70 +
        2220497322841985524516659987717460796418527918512804338704672451891026) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 24 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_197 :
    recurrence5Scalar1Left.coeff 197 =
      ((((((7459900207 * 10 ^ 70 +
        4704026290114958193365463802198474610988819666588996890695134527320914) * 10 ^ 70 +
        1538403161758673335999710772156025952347735099174032536652140733971087) * 10 ^ 70 +
        6760459580685988782170822642867584601841511247468282516912722826795404) * 10 ^ 70 +
        0922488570474394739354781081552976280063911802820413982539991928803110) * 10 ^ 70 +
        2205693332116837455548096274084176839520825257397315096981144665617006) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 25 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_198 :
    recurrence5Scalar1Left.coeff 198 =
      -((((((8992125056 * 10 ^ 70 +
        7227868584539047439045370557430167435906634618509689774002397267196057) * 10 ^ 70 +
        1957238211234689652471261843812014908790497680344170324795444128776411) * 10 ^ 70 +
        9844191760620342915151009061184787404827073238728508898945707422524713) * 10 ^ 70 +
        8508046095233023777543411294133187530520206778079468459498635904507974) * 10 ^ 70 +
        6514431022590020617499795521461717758547434314227067501109139228799467) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 26 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_199 :
    recurrence5Scalar1Left.coeff 199 =
      ((((((10651799012 * 10 ^ 70 +
        4217283577198090089162862588088820234846756033859360707290508908262001) * 10 ^ 70 +
        1959866456529589237909723189489925239939844969322742905862705333266991) * 10 ^ 70 +
        8116530703636953952898417834938841285375030692576598815325081628147438) * 10 ^ 70 +
        9741926538859736535084792387455126773335088944658958655402752202087361) * 10 ^ 70 +
        7529952942665461262449974703652607044604737155882770873311842640521821) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 27 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_200 :
    recurrence5Scalar1Left.coeff 200 =
      -((((((12399142582 * 10 ^ 70 +
        7705220671262025097937930517196102402066448722520043067983290694721358) * 10 ^ 70 +
        8740480869417744594608838381597027909680637336427442247982308911757295) * 10 ^ 70 +
        5792295687882874022791135083318208428765696196657808475192741429452334) * 10 ^ 70 +
        5265111800002389694320424864378634330815836688208534877981111359692666) * 10 ^ 70 +
        1340102618870379136360283340627521449475678678045031824487569873279575) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 28 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_201 :
    recurrence5Scalar1Left.coeff 201 =
      ((((((14182113536 * 10 ^ 70 +
        7454979246472530042358575638384040885979118070675473290295879221355902) * 10 ^ 70 +
        6688421418640335759354671430480282631714399420372959747186109147338705) * 10 ^ 70 +
        4083262903198952935219566738214029346628765711021069473901296362968840) * 10 ^ 70 +
        6927711112588468214622692876665643717978350927520227649096242366744774) * 10 ^ 70 +
        9560036074138257805693666773578057160038566093437686631622072600408375) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 29 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_202 :
    recurrence5Scalar1Left.coeff 202 =
      -((((((15938176265 * 10 ^ 70 +
        4727493264491200028427581930213306698189286703100184004556595246273455) * 10 ^ 70 +
        4515302123957354227390325860250222945204250049364308899462215592119101) * 10 ^ 70 +
        6290637420147061403043720961289186815775600495352352713695990476130123) * 10 ^ 70 +
        0435765116540452258687922827795996004631327059589205758006759755670620) * 10 ^ 70 +
        7738187384263229851975698670350551345359406954192205428439407022608606) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 30 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_203 :
    recurrence5Scalar1Left.coeff 203 =
      ((((((17597335518 * 10 ^ 70 +
        3664053495778763353182523058905752630682137831033729152367949510926229) * 10 ^ 70 +
        0062386055577726611142403214494616714872090646217888485388333821944528) * 10 ^ 70 +
        3474184965843377773834173914925342062631216211248636175064886336861405) * 10 ^ 70 +
        3906628090350253846904303905901653791949086905549144027447765298296649) * 10 ^ 70 +
        2194465196072922721633637095315028339072985794340408190981468134589761) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 31 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_204 :
    recurrence5Scalar1Left.coeff 204 =
      -((((((19086299928 * 10 ^ 70 +
        4719007419731700851625272439269565651454673064442232462045314179958961) * 10 ^ 70 +
        6187651102355959222152139720006806967547045364272148439463739712608782) * 10 ^ 70 +
        3878415975015330148590858361726994387376496331599516619873779285756627) * 10 ^ 70 +
        0201263865046807076224900856321694761204913870801418818655298371809055) * 10 ^ 70 +
        9854069137823906635137929872046777249839167477233720790757912480616319) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 32 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_205 :
    recurrence5Scalar1Left.coeff 205 =
      ((((((20333477877 * 10 ^ 70 +
        0780754384702656608337441862889594311906231328296005894540786040390159) * 10 ^ 70 +
        3040948420058792184422818147597742324691846760545446238467814049310273) * 10 ^ 70 +
        2509436971249528055905993959973023145920399363998991625032382892353857) * 10 ^ 70 +
        2745362119280667144028871754900065913444528328924416204084495443110023) * 10 ^ 70 +
        1870756954452847605921308000272027150756470909868746247552525317092124) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 33 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_206 :
    recurrence5Scalar1Left.coeff 206 =
      -((((((21274365246 * 10 ^ 70 +
        1928771579576181067904333474029189094963089384365952596527546744422815) * 10 ^ 70 +
        5006054034777229951284767793302870716872860400198996482287415574338443) * 10 ^ 70 +
        6381667421286649010508061872027775875614193289178450070603506252057624) * 10 ^ 70 +
        8667183630812417425193338458638959746022258943227502779678723978367554) * 10 ^ 70 +
        9966499080433230685979802852121930869382735993617111460917120723352809) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 34 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_207 :
    recurrence5Scalar1Left.coeff 207 =
      ((((((21856786812 * 10 ^ 70 +
        3597290782214578589873497715975025813259223496086890503730816041052469) * 10 ^ 70 +
        5797476706987025215244036942546672539541610714858195818087135166933329) * 10 ^ 70 +
        6570466570781327234565775382079032126133854900318397773961602492299010) * 10 ^ 70 +
        1090306444832963934315614447296110390531626519390123509156911030611838) * 10 ^ 70 +
        7106335633719992612394572736077928845752779510506198651313548324388868) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 35 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_208 :
    recurrence5Scalar1Left.coeff 208 =
      -((((((22045420958 * 10 ^ 70 +
        0810821222183551104124621339777340224771644359833758062155768915801441) * 10 ^ 70 +
        9057980063292805260297054208318675651383317133231689009469778287673907) * 10 ^ 70 +
        9435394557810601046880958779649637107089238208087272865924779763740288) * 10 ^ 70 +
        8125891711252391601249225613402060706213869869948866277981841456596537) * 10 ^ 70 +
        6571352997986762637977564844134887550910490904932106420880932358943672) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 36 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_209 :
    recurrence5Scalar1Left.coeff 209 =
      ((((((21825082244 * 10 ^ 70 +
        6447146541112483026515500188024368267467684386702439164885748695677008) * 10 ^ 70 +
        8858214712050617521498530601677702464442626388929877426527102830090008) * 10 ^ 70 +
        0338753670974556342819503109096899065526702233741090220893954928820168) * 10 ^ 70 +
        9492079578007906218861990204597471769963805098565867841106976048273335) * 10 ^ 70 +
        5716665984934019529047689386277929204052454716308227919472163748745517) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 37 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_210 :
    recurrence5Scalar1Left.coeff 210 =
      -((((((21202357140 * 10 ^ 70 +
        3413107336121068669073259831926005522016995889313462695600644950245628) * 10 ^ 70 +
        5514421947842583811346138518958037190676362541729113389281710740110925) * 10 ^ 70 +
        1924947374208946502823501119325114111343424616283662485564111476149443) * 10 ^ 70 +
        0199639273655341360026586345468142498166787209734983400890935673407972) * 10 ^ 70 +
        2024603746794692510119126535575983583572669129988994764182275137079666) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 38 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_211 :
    recurrence5Scalar1Left.coeff 211 =
      ((((((20205370726 * 10 ^ 70 +
        0357027450373992618238647366469506959351490415736321073253563342997831) * 10 ^ 70 +
        5361714319159367613775229174173975441377875092962078277269067999613237) * 10 ^ 70 +
        3991963775030979278386091215166255791068431803671083399485345325005127) * 10 ^ 70 +
        6845043936093718824748291798094797021919591511002032489816460574973899) * 10 ^ 70 +
        8120164931255406686162052723732733685602410036776723282377609242998611) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 39 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_212 :
    recurrence5Scalar1Left.coeff 212 =
      -((((((18881681195 * 10 ^ 70 +
        1722080085283005282009205624709317407219802226503730070723896727711525) * 10 ^ 70 +
        7964958856548754836007791506784537231356867123517942049304612524934963) * 10 ^ 70 +
        2794552725730187969905864831268471935017538114289745147463300812400249) * 10 ^ 70 +
        5855700368797556201305170158293476442207490534955519392417591377616782) * 10 ^ 70 +
        6219357850565027667395561303986091326768605359689390818332086555513125) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 40 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_213 :
    recurrence5Scalar1Left.coeff 213 =
      ((((((17294522097 * 10 ^ 70 +
        5759496915301812417530609101480759876298218925771322282249078116290207) * 10 ^ 70 +
        3274168915724157305680410686267435277508953719301380867017867739735249) * 10 ^ 70 +
        7854774084361968058954764234486840548489011187362046479936384544136640) * 10 ^ 70 +
        9822629436622569216343062112717215659162551298644391140206686380978866) * 10 ^ 70 +
        7769965046191021843342747234624107748263832073249409898695449776159906) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 41 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_214 :
    recurrence5Scalar1Left.coeff 214 =
      -((((((15517805932 * 10 ^ 70 +
        7457688403666448188637272821491791893708774112677580519471599864975659) * 10 ^ 70 +
        6066733270862857780069737316213139125848772943012393794104084682368095) * 10 ^ 70 +
        3608374215960965898238265259719040096101403899400645462208195838387652) * 10 ^ 70 +
        4277711820798194524886063188404518015272353651624997740421256958161324) * 10 ^ 70 +
        4264503406853231979939155212994775781847275131982562820276132082646061) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 42 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_215 :
    recurrence5Scalar1Left.coeff 215 =
      ((((((13630438083 * 10 ^ 70 +
        0949276178227424082627634799111686205747105719042109275034136728088166) * 10 ^ 70 +
        5856699669882939773048688327383287669273688117816708783030710538416175) * 10 ^ 70 +
        7925270567011975198512185974047723782155612232072055396876358024683713) * 10 ^ 70 +
        8473162345167222916815073336470152173343528648136929571574675501437426) * 10 ^ 70 +
        6406924209802656608087245435102824691989702262262072816931079892502386) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 43 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_216 :
    recurrence5Scalar1Left.coeff 216 =
      -((((((11710548385 * 10 ^ 70 +
        3658077047365930064872827670154717756406746346543067513500506025647655) * 10 ^ 70 +
        0075093149131475305366100530928058324853302628991824246836619815138097) * 10 ^ 70 +
        1844740381739697792526058889166430151997996531833130080954735808845507) * 10 ^ 70 +
        6611208242853564692935574857107990823580943240160430635793061650520918) * 10 ^ 70 +
        7557391598154973336244016049384345597930185016268861248308869085847790) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 44 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_217 :
    recurrence5Scalar1Left.coeff 217 =
      ((((((9830223211 * 10 ^ 70 +
        9688266258502024369788552973456468279503129143532246277172908159199040) * 10 ^ 70 +
        8156793668446174150402831653688698789850250690468278976432673179924159) * 10 ^ 70 +
        8566359389675192097001063034430438161169534040190118750769404092463666) * 10 ^ 70 +
        4493768061578358121674375497327306415194136155203192983561843798849049) * 10 ^ 70 +
        5662995157584418677886880654641846246555504380200475771224398459038115) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 45 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_218 :
    recurrence5Scalar1Left.coeff 218 =
      -((((((8051221786 * 10 ^ 70 +
        9481712379328808835967725297265230554147436576524262483804647213290881) * 10 ^ 70 +
        9805612114057939541325319804036612541325256989238774642238846179487807) * 10 ^ 70 +
        2019184998663205717106120078638943866478148628932177125894274790922879) * 10 ^ 70 +
        0607421346806586269529064472029096856256983303161138768416791877096962) * 10 ^ 70 +
        0549260006551320302407274419582591964315302322763763619610381562749374) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 46 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_219 :
    recurrence5Scalar1Left.coeff 219 =
      ((((((6422006151 * 10 ^ 70 +
        2049332713148589647440644140509934709576731291144117291992968330983099) * 10 ^ 70 +
        1264077722751181858003184066191082080194800854821694984743583234354218) * 10 ^ 70 +
        7902523939399608615418072339789560202596882893197006380549925449203392) * 10 ^ 70 +
        7990187936741601009490918879899992636875033636335898929853917244265434) * 10 ^ 70 +
        5517757556982167910271998666284978355012285645369731371441761720344756) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 47 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_220 :
    recurrence5Scalar1Left.coeff 220 =
      -((((((4976231616 * 10 ^ 70 +
        6641789918333244158588941607382349748543784833171151163610247232365763) * 10 ^ 70 +
        5374374691469292578780643568543456130963334998641366923884464959509456) * 10 ^ 70 +
        3748331796959868312287485679390801048044536723326168024532163487035731) * 10 ^ 70 +
        5437639116464986244106662861783164098350825894735483601105635839319727) * 10 ^ 70 +
        6376011116889451276317659564772705034793898181021419675244957143495894) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 48 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_221 :
    recurrence5Scalar1Left.coeff 221 =
      ((((((3732662665 * 10 ^ 70 +
        9717412388835706624024766190330828389445053517965929622488902514441154) * 10 ^ 70 +
        3892029122167822169141700496712129321225773018786640847955546220061869) * 10 ^ 70 +
        6474801047434676022986802303766319397260368215694487326070187867367492) * 10 ^ 70 +
        1528481690877186491924060311653052104943202772358945381886730277963984) * 10 ^ 70 +
        6529604913065745525615395030338536073507043823880055470104728994754274) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 49 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_222 :
    recurrence5Scalar1Left.coeff 222 =
      -((((((2696323878 * 10 ^ 70 +
        0857603042550544811749488628655515456194835922758051207803597703021292) * 10 ^ 70 +
        3227305320129384222263081392166742282960388690528363347959069505383255) * 10 ^ 70 +
        0355218243979690683725095891601160508921057564529319366267916273372569) * 10 ^ 70 +
        4620053960508002371752460426739924925985076233314308661468689304078769) * 10 ^ 70 +
        3880737474691090819110195081632494068705521873716784247649798032114285) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 50 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar1Left_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
