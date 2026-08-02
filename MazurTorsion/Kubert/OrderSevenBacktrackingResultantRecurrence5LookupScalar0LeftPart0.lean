/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Left coefficient convolution

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

theorem recurrence5Scalar0Left_coeff_0 :
    recurrence5Scalar0Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_1 :
    recurrence5Scalar0Left.coeff 1 =
      ((57838809210387311374847545185027900089879989385612125 * 10 ^ 70 +
        6384469871949651332869024275032357497219488186425400442200125916446720) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_2 :
    recurrence5Scalar0Left.coeff 2 =
      -((214859657058788137561931875010942639075650965981427710550 * 10 ^ 70 +
        3798751301650443317761350860180649458767504418948508399685065446457344) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_3 :
    recurrence5Scalar0Left.coeff 3 =
      ((1085142511749854408611013137502453146191217497626392913179061 * 10 ^ 70 +
        5383472627850869671723771681176355184781097799354635692793977600051712) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_4 :
    recurrence5Scalar0Left.coeff 4 =
      -((6407024206839397468831322209262957814513218904501033638931835670 * 10 ^ 70 +
        3828052817746906507941539092349729854394602837243484125786688129163840) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_5 :
    recurrence5Scalar0Left.coeff 5 =
      ((18184453663833481562539384941366872449516123777942740814226710884567 * 10 ^ 70 +
        7600143948384809118549203092651526390454160749804740043965063304766336) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_6 :
    recurrence5Scalar0Left.coeff 6 =
      -(((5 * 10 ^ 70 +
        4624182182072415980154228589168929825891295246571407242081487002144290) * 10 ^ 70 +
        9013762694992147445436387245278762956551462520907311614540100826242320) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_7 :
    recurrence5Scalar0Left.coeff 7 =
      (((15522 * 10 ^ 70 +
        9186681163327273639550681624198229555478156149827041673060981696743348) * 10 ^ 70 +
        3031615858950707482913275636696089926854942047142830611987685503772096) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_8 :
    recurrence5Scalar0Left.coeff 8 =
      -(((30714221 * 10 ^ 70 +
        7362368117893725343633680599497290015916753920664805181120210819190548) * 10 ^ 70 +
        8712515907888336958632128189115084638152036893437526975029442421920448) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_9 :
    recurrence5Scalar0Left.coeff 9 =
      (((42377001876 * 10 ^ 70 +
        8816914087402997818501039461815637911621918476236515733304681641947051) * 10 ^ 70 +
        1800984884024059781298544860640375737127469237891929328462201786612288) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_10 :
    recurrence5Scalar0Left.coeff 10 =
      -(((40944803542317 * 10 ^ 70 +
        2958733643972558217799231773502445056849172156969534064308707738412379) * 10 ^ 70 +
        3286045003714471009083906899741396036832662232482138430207594338190880) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_11 :
    recurrence5Scalar0Left.coeff 11 =
      (((26423176047769460 * 10 ^ 70 +
        7378549365530050471126057253218856291673142458462400442211113172593195) * 10 ^ 70 +
        5391427527698069699656144981223613773223643478439313192238666449339296) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_12 :
    recurrence5Scalar0Left.coeff 12 =
      -(((8467949333360283741 * 10 ^ 70 +
        7848550568665293326712999762320246761337665151938048366759408458326722) * 10 ^ 70 +
        4983397543340064979082925358137901821965908089176559115404576051966624) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_13 :
    recurrence5Scalar0Left.coeff 13 =
      -(((3241688990876179535064 * 10 ^ 70 +
        6214960983220743009767987795345444507785485718474250138571546916054549) * 10 ^ 70 +
        3564303431136508160776089706952292905269342002996274344940560682720736) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_14 :
    recurrence5Scalar0Left.coeff 14 =
      (((6307156327432314063861240 * 10 ^ 70 +
        0574279761034601676339150908696795538085857419113520442837268731940965) * 10 ^ 70 +
        8154051702915548848676630872272241594501260311222912442247200008643248) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_15 :
    recurrence5Scalar0Left.coeff 15 =
      -(((4373341892313278744194778391 * 10 ^ 70 +
        1491077381420807601729087662678406660569823298065582719822546930514407) * 10 ^ 70 +
        0566382506741916623960840108499505753676677121542830387859028589368792) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_16 :
    recurrence5Scalar0Left.coeff 16 =
      (((1732695035741687314438453131046 * 10 ^ 70 +
        0276157500821395740930129777567039628233462027059286283604572013409467) * 10 ^ 70 +
        3664766909386540826085762229670543618720650737791028155828767310471992) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_17 :
    recurrence5Scalar0Left.coeff 17 =
      -(((257591763491188620383812670561266 * 10 ^ 70 +
        7685734290702847402094418436937292262091117115736140238471314474692827) * 10 ^ 70 +
        5793806023381033280504708172572465511898891932233098311839244957557712) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_18 :
    recurrence5Scalar0Left.coeff 18 =
      -(((160584630796853957598065813587322194 * 10 ^ 70 +
        0390396249574391288959981760896221511833199590584928804087022763198952) * 10 ^ 70 +
        1054418309022983935043676566190462600404745545910528421259091714913460) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_19 :
    recurrence5Scalar0Left.coeff 19 =
      (((141128814158712407665408487709589681213 * 10 ^ 70 +
        6695288222534086470252420030918680389074560022268822089016330786586936) * 10 ^ 70 +
        5577587037115515732335499072914413884305822465031270628574852875285712) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_20 :
    recurrence5Scalar0Left.coeff 20 =
      -(((59437201353679910656062490446098107573591 * 10 ^ 70 +
        0638961485195206778780802033556290502730735171296318521608720755923031) * 10 ^ 70 +
        6019990632502913148020836197187971640559450050956391170321672657455824) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_21 :
    recurrence5Scalar0Left.coeff 21 =
      (((16247824325413788906687299537563830205879985 * 10 ^ 70 +
        1758799885328331352936342245568372391691680846798973523791324472470987) * 10 ^ 70 +
        5302500773693833545886161487056697479880022458589637420424452220670532) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_22 :
    recurrence5Scalar0Left.coeff 22 =
      -(((3244323955020597442234256191572274927483910226 * 10 ^ 70 +
        7505171715464116570319562354494723931033344066253227744736294350408442) * 10 ^ 70 +
        4826400294924385999420485867197225737550103026329540069777387206001296) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_23 :
    recurrence5Scalar0Left.coeff 23 =
      (((922653564063497552451268684699449650040968680311 * 10 ^ 70 +
        2362045057234255864239838274096651125641228973130913041415119811244983) * 10 ^ 70 +
        3875130889234901194680879010698631490286170088926285252726309735400848) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_24 :
    recurrence5Scalar0Left.coeff 24 =
      -(((612706296652840296176002773187744634241044092502821 * 10 ^ 70 +
        9604937478467251851212395579126941043980032197622951231190087944883515) * 10 ^ 70 +
        5596024925621086628765016969589397183827901618644499200928672489253009) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_25 :
    recurrence5Scalar0Left.coeff 25 =
      (((392973756619229120330396208436189418433755919495434710 * 10 ^ 70 +
        7729480605319105555360331174718990757242771813125297617215095060136139) * 10 ^ 70 +
        1977982073648023484685902568628788445143476473611127886798508275986242) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_26 :
    recurrence5Scalar0Left.coeff 26 =
      -(((191608923147894235373791539589996443460014512228230433250 * 10 ^ 70 +
        4732080381188940037424490074422121077483393509842518942452616256949434) * 10 ^ 70 +
        1416267996741883412717130786108737322060018173079397109096434780291081) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_27 :
    recurrence5Scalar0Left.coeff 27 =
      (((73688963973489933438803607179348325649920482942368248676231 * 10 ^ 70 +
        9055969681745741317029819036081326974366329796970692259167344802424193) * 10 ^ 70 +
        8585294018364828043106246996981110433658264571531164000007744358522152) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_28 :
    recurrence5Scalar0Left.coeff 28 =
      -(((23317656259246288279075768996100285927524968349417366212637515 * 10 ^ 70 +
        1091791555085814984708852824059635037220258611952720147653018027259599) * 10 ^ 70 +
        9735840268229879489819727969377573095498647761383514210695638178225158) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_29 :
    recurrence5Scalar0Left.coeff 29 =
      (((6238814095739936853669048940902931249536662023758966415631528580 * 10 ^ 70 +
        7940351567006161112921934114491841484519734794566197361621403491644720) * 10 ^ 70 +
        2450714686232709145920153230479307990577009881422890136513714882067254) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_30 :
    recurrence5Scalar0Left.coeff 30 =
      -(((1434164120997137466304263150585658756215481671980660986261849056999 * 10 ^ 70 +
        5703575335674206650453412506843256278108191362623272606028968753047267) * 10 ^ 70 +
        8709919067676537741682557991933351746863318192735107309120850331570391) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_31 :
    recurrence5Scalar0Left.coeff 31 =
      (((285428172594353518032321055053041673733532784780921003679237780082765 * 10 ^ 70 +
        5177577529792627235977918987202868299935136128550661563872068808571622) * 10 ^ 70 +
        8558532045473608548451890086480416036039783079738817721429829452443090) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_32 :
    recurrence5Scalar0Left.coeff 32 =
      -((((4 * 10 ^ 70 +
        9167761854470617730149071045540950207819705893163053555535782793211656) * 10 ^ 70 +
        5363553866127148197667628149700556333114417732627572378197856844392645) * 10 ^ 70 +
        0934586645052585517847822646140927221998906242212881842627983460940890) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_33 :
    recurrence5Scalar0Left.coeff 33 =
      ((((724 * 10 ^ 70 +
        8980907526175200932267444181949011433607920303473931851979173195962385) * 10 ^ 70 +
        7694127125748946301118508321734623089271881476450339160987038431494754) * 10 ^ 70 +
        3167451907127515307684473091230404366726463018065679615566024335494303) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_34 :
    recurrence5Scalar0Left.coeff 34 =
      -((((88429 * 10 ^ 70 +
        5414695750263183855783675123828243525456263856043470950531460104249160) * 10 ^ 70 +
        9655288752857447030957167516869494513887647781858917755825756191576684) * 10 ^ 70 +
        7372780994873221046426931094520640211293678393938173968469915916887120) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_35 :
    recurrence5Scalar0Left.coeff 35 =
      ((((8032713 * 10 ^ 70 +
        1235546775521905328808135745924193729826245659079729340276747537345893) * 10 ^ 70 +
        8808174924027054550577750204498250710054495378965513532276159478511384) * 10 ^ 70 +
        4315825102958905310425967855985977252847275444652444211746273087805606) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_36 :
    recurrence5Scalar0Left.coeff 36 =
      -((((285385766 * 10 ^ 70 +
        7220081699567460877968418302262698851637088462307545028757839474037648) * 10 ^ 70 +
        8365785118849897558143984872670435194883944580657098651759415405560735) * 10 ^ 70 +
        5775502609850202951260371119335467919108153652924057336459540565863783) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_37 :
    recurrence5Scalar0Left.coeff 37 =
      -((((82084280403 * 10 ^ 70 +
        5125837907615361911967195955669418640742773052837590051011110143095326) * 10 ^ 70 +
        4264399809971230379351717722171098502492461919402981270524548488231571) * 10 ^ 70 +
        6694943162446785679832487968138401748236959424912464286809532777569859) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_38 :
    recurrence5Scalar0Left.coeff 38 =
      ((((25341885162099 * 10 ^ 70 +
        9921741178498199835020438738660027989311208798595959091293306739235013) * 10 ^ 70 +
        7663324476323510665519310161566087403926716487893521250316593240765693) * 10 ^ 70 +
        7771010670714074430592342247463715792851284264870546082536899282745650) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_39 :
    recurrence5Scalar0Left.coeff 39 =
      -((((4684799677822433 * 10 ^ 70 +
        9515406859002591832353697628579024421583006819282829037014601812946779) * 10 ^ 70 +
        6501900786188930643959439135263078826124943774299862953940828773256716) * 10 ^ 70 +
        8770532040313878586502458333477324884328533886376260571546298849531229) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_40 :
    recurrence5Scalar0Left.coeff 40 =
      ((((692906812600109827 * 10 ^ 70 +
        0580123577701021484987889905871283414240446534418937376300597710730957) * 10 ^ 70 +
        6758604395992216933455916059340169668539532853654572909061057244489651) * 10 ^ 70 +
        9147666526065649362615995108265867529171182102635245166237961704004388) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_41 :
    recurrence5Scalar0Left.coeff 41 =
      -((((88416617840560445036 * 10 ^ 70 +
        5262436373480083847158647514348375416780746208923174651079578495812689) * 10 ^ 70 +
        0782642866232624202731993840091417638035785839336905450151433784765098) * 10 ^ 70 +
        4242063919544123096217167202726327791608519377960829157444401437009778) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_42 :
    recurrence5Scalar0Left.coeff 42 =
      ((((10049692516837084945660 * 10 ^ 70 +
        3833906891324963539898944494384970445198790007022362102601479113784893) * 10 ^ 70 +
        7914497329740894794976141721760486048652985932957298457136214050160319) * 10 ^ 70 +
        6752939484506392179325462427236904089696545146643641146203854924582706) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_43 :
    recurrence5Scalar0Left.coeff 43 =
      -((((1035012424864128258689326 * 10 ^ 70 +
        0581512981611226241524712631450076233089519953578570493994432628265553) * 10 ^ 70 +
        4728604208865300175831747503366918158645508191374451141714121952303110) * 10 ^ 70 +
        2084022811723549405148681073714182131245729836430792775238863536941285) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_44 :
    recurrence5Scalar0Left.coeff 44 =
      ((((97605317598992059162019569 * 10 ^ 70 +
        1725705298061238531417234066954206839477368611016347714150448948657389) * 10 ^ 70 +
        2879615884021805128210605005241611778058922874460021370345071655077435) * 10 ^ 70 +
        0774707971500177593570685778401952854904658610956820751157961904263661) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_45 :
    recurrence5Scalar0Left.coeff 45 =
      -((((8488464654391983141095818529 * 10 ^ 70 +
        3498274589184368797519652424835455160789409840937248716445376908811638) * 10 ^ 70 +
        0948012278416972318279447467477651333830547031935811966070361661128738) * 10 ^ 70 +
        1706312022328944877939044100846882549372954507260581156785866454207027) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_46 :
    recurrence5Scalar0Left.coeff 46 =
      ((((684326166260522332709663726418 * 10 ^ 70 +
        0437871806108471397245337860485028406373727867089161924958255552312080) * 10 ^ 70 +
        4797686122289164144248338554463811943226116834039401385291187520040937) * 10 ^ 70 +
        0330028026056209656188211667358634261237668010888373023263331212289234) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_47 :
    recurrence5Scalar0Left.coeff 47 =
      -((((51345533104515856418171675025953 * 10 ^ 70 +
        1337620821572636618979762965802771929758230915075353311165180438685095) * 10 ^ 70 +
        6250684364794822581143114442675212885072326454383232146024492689365745) * 10 ^ 70 +
        0499922245352514511708829700841539900465329667140453765496732880102040) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_48 :
    recurrence5Scalar0Left.coeff 48 =
      ((((3596898081113178570493662539112440 * 10 ^ 70 +
        6668407071766138685751525855877342755343330769815924659553756868860708) * 10 ^ 70 +
        1473915365210899258235553466715393870836442240537252492139885166853800) * 10 ^ 70 +
        5118388448788126188599284517399019210113201758119174747001149588839650) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_49 :
    recurrence5Scalar0Left.coeff 49 =
      -((((235872798830641794883112420709755261 * 10 ^ 70 +
        3867707103319940720057165534019793813258190307094752564714539729777991) * 10 ^ 70 +
        3726060438885101749345979241219754186343715493678618784852225122864032) * 10 ^ 70 +
        2182612609625012007958862570115403248758773857357785396705449832424170) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_50 :
    recurrence5Scalar0Left.coeff 50 =
      ((((14511536614642319656305937062819221018 * 10 ^ 70 +
        8454781100281107202849765429729446141104134947449891851467604574364302) * 10 ^ 70 +
        6624447012875413397624267898850934120541197678313321072265991713842207) * 10 ^ 70 +
        8335023364387003105980862219675215279126504530313633854476277672092878) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_51 :
    recurrence5Scalar0Left.coeff 51 =
      -((((839193369858612770028683986836548674496 * 10 ^ 70 +
        8010357916580047166399500562541597770047932296729560497047943592959839) * 10 ^ 70 +
        3316647495852768170841457168866409617773147400104987677386106588231294) * 10 ^ 70 +
        1711579425132042770830190823951952567764232191081404041603357994594087) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_52 :
    recurrence5Scalar0Left.coeff 52 =
      ((((45692545584787154228663181837095247913873 * 10 ^ 70 +
        8595725632599243475667646094033871287558782872618461093146270603772548) * 10 ^ 70 +
        6840204849050028897594221039626970910475452910101066283033340325728672) * 10 ^ 70 +
        5383132293164744833509397591460238436870664932448782695690057536289088) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_53 :
    recurrence5Scalar0Left.coeff 53 =
      -((((2345842061115191167041138651315225346476514 * 10 ^ 70 +
        3612091710709028947710193783270019532200957436704918335332709451029889) * 10 ^ 70 +
        4486523168066680308032332087443810958942814589332979017549444707395740) * 10 ^ 70 +
        4282343328249201355915319449610223177578944450632158473790111111572026) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_54 :
    recurrence5Scalar0Left.coeff 54 =
      ((((113706470057370749866914645431835647417750908 * 10 ^ 70 +
        8394707679897137659707984582920155506128336376200310952697411258149298) * 10 ^ 70 +
        5662303957807250798037820077438715652671406306371796856338054474933581) * 10 ^ 70 +
        0853713490727788479836471242891042636060775710482471571520733928911517) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_55 :
    recurrence5Scalar0Left.coeff 55 =
      -((((5209598560543462613490079816766414203185960704 * 10 ^ 70 +
        9986136939825963990563558087874103505888368754722250056879949712800326) * 10 ^ 70 +
        5797638765662777671884428465157254954611881535687115878298227063532165) * 10 ^ 70 +
        7628718143992072446003644757105117130925838089371582331375086652244186) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_56 :
    recurrence5Scalar0Left.coeff 56 =
      ((((225838854116677468570554085455756330048696118951 * 10 ^ 70 +
        6235012005985630419252927708772627588190482002248887231208892678036221) * 10 ^ 70 +
        3357866050068891126505192332731751322788393934179923745612000283903133) * 10 ^ 70 +
        6651354369190195613597744276069664328666202523657237063292886836728233) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_57 :
    recurrence5Scalar0Left.coeff 57 =
      -((((9271662973507513964150138915581689460153551795903 * 10 ^ 70 +
        7401881556866967012312335096484263374994781533930874472904684197064718) * 10 ^ 70 +
        6193696919011044964003273987631150429510349755475083826036704853451483) * 10 ^ 70 +
        7590533657446630776200295636267433037174139268655396051311636971177374) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_58 :
    recurrence5Scalar0Left.coeff 58 =
      ((((360760052469647350587572423175337972432350731477649 * 10 ^ 70 +
        9900541812952250782395902700062706030946434717648293842021888637207516) * 10 ^ 70 +
        0194378223338558625148061133976960628179527125429269746162121669488653) * 10 ^ 70 +
        4005979806762291223305583049246619623208138867355821738943790771452236) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_59 :
    recurrence5Scalar0Left.coeff 59 =
      -((((13312682329719098731058079546467482449378634244939029 * 10 ^ 70 +
        2889205389825055062345643009740075070409497981591915883925945833629025) * 10 ^ 70 +
        3972012900433570769938468293835865006704242633320942570808352837544009) * 10 ^ 70 +
        9446414882011942009519958011408623259911868397952761722030404597014647) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_60 :
    recurrence5Scalar0Left.coeff 60 =
      ((((466152065290932788497529395312990372449297293115048103 * 10 ^ 70 +
        5975828628812866112827718144823155958254877161626687138213172635573889) * 10 ^ 70 +
        8001915271035098512364603767590100878862040456949756972111351256408161) * 10 ^ 70 +
        4677667895843853802651842353860942640731923596333651115094057197076373) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_61 :
    recurrence5Scalar0Left.coeff 61 =
      -((((15494276300836585846434394294802438434678218930170883481 * 10 ^ 70 +
        0398285660850298628443384544450052596734973720853478869497221160933738) * 10 ^ 70 +
        6520872901590986220077924633019781855242348964821573122203321562668418) * 10 ^ 70 +
        6365363415306544560783227785182722516078055826728303285148640231087884) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_62 :
    recurrence5Scalar0Left.coeff 62 =
      ((((488980791635385797318768717916278584805650122654241319576 * 10 ^ 70 +
        6037185736165874943984282932379527600749038729510156678162208461116439) * 10 ^ 70 +
        8610215893074005012930254871541293449671799113713924891611441788389202) * 10 ^ 70 +
        8083822054332465386727532569054815373376374527122064106017107354192458) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_63 :
    recurrence5Scalar0Left.coeff 63 =
      -((((14652034175947478149715708070873840108013483964136047644628 * 10 ^ 70 +
        2186241326444385393128868976241397156779409660849281215152210754721894) * 10 ^ 70 +
        6900791445899252064825046196914727368453278446222214723238118947934866) * 10 ^ 70 +
        0873813968388462001907034234935131855460677370283531750901683561395311) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_64 :
    recurrence5Scalar0Left.coeff 64 =
      ((((416763479516209234780022906078823664729975809387477570751327 * 10 ^ 70 +
        3379367741387321176707572218548669536754504769223152764122420385228331) * 10 ^ 70 +
        6593262772028818130187667780817455000012478579528120324001242594383884) * 10 ^ 70 +
        0068114255326261369445762116429638729675162243666955758074436461953963) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_65 :
    recurrence5Scalar0Left.coeff 65 =
      -((((11246671262529430102540909033388744677184044148816923083549193 * 10 ^ 70 +
        2701273460741040207244093663858206766417164390840695788653832166754399) * 10 ^ 70 +
        7141035172861125648094778586157632060646878305228191562847997183376606) * 10 ^ 70 +
        4932805543410581140180723551531225315041144188426709741985318289502879) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_66 :
    recurrence5Scalar0Left.coeff 66 =
      ((((287648305553002919633134204337291301310752643055095597420539389 * 10 ^ 70 +
        5871800877023013336769575047879430736658614794964407533486552347113515) * 10 ^ 70 +
        4810903001313664801591058909907375276952196576044185359810583474468180) * 10 ^ 70 +
        4446729385251898319220819285045864520988556652348337592528931093692874) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_67 :
    recurrence5Scalar0Left.coeff 67 =
      -((((6961171848130048714484517219058883060143599701529571315365317298 * 10 ^ 70 +
        8779142370935281907173668014974788562580726978615159562929743288544507) * 10 ^ 70 +
        1590434634550268756587920238552176791194212078419861143545797184087093) * 10 ^ 70 +
        9490834771359892077432600621839205872454465315771340167740658459786684) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_68 :
    recurrence5Scalar0Left.coeff 68 =
      ((((158978925594333803977150002002886142437269682880624147302456216262 * 10 ^ 70 +
        9503300517923723385313333972252436498475001513521107883083449080631946) * 10 ^ 70 +
        2830645485090155706474769264513032287812673659578646558112463104918824) * 10 ^ 70 +
        9942977986109382240683670771473896604559997238375814113560773531970748) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_69 :
    recurrence5Scalar0Left.coeff 69 =
      -((((3411977030268802720367220494681585732844971229684769661796956177028 * 10 ^ 70 +
        0687767517036616655830752596587748035935169131245259782424494300428381) * 10 ^ 70 +
        7498301610857525992426659398292468499650709799778628068981141508876639) * 10 ^ 70 +
        8178521682044712439302097728684898648926306435411867758606081938825171) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_70 :
    recurrence5Scalar0Left.coeff 70 =
      ((((68340957516527985794434318023251451377657512806453859454420322571371 * 10 ^ 70 +
        5655314584949466896842806248060478644117038163740065789735236317879770) * 10 ^ 70 +
        8518553707044029134584545074145434747755736605424537688612863616174515) * 10 ^ 70 +
        5783838633238234245222339613654670141258054701627194900638652541952461) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_71 :
    recurrence5Scalar0Left.coeff 71 =
      -((((1262235619833756288479926380003179855822431444951069813494332769827254 * 10 ^ 70 +
        2653708471202410897826052151613797024792072728663607448167346539644887) * 10 ^ 70 +
        5762641367710199686833287405127679706439944766260014881768233193467611) * 10 ^ 70 +
        7030930173654765343926218682447976537980444583738384456158012183034646) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_72 :
    recurrence5Scalar0Left.coeff 72 =
      (((((2 * 10 ^ 70 +
        1006217070116358027564381508305579024695454728239400455242661336655702) * 10 ^ 70 +
        1119010881665403947628621460621787122707266808641216979615964549929750) * 10 ^ 70 +
        3018589749375983153307929872001315959963474428836975704602088340828088) * 10 ^ 70 +
        0064178997551876922269615350713361239321422927822396891493757891226923) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_73 :
    recurrence5Scalar0Left.coeff 73 =
      -(((((29 * 10 ^ 70 +
        8841804242482120663961340773437855639861419080171948345604399852445723) * 10 ^ 70 +
        0600489668440420262867421286349746335943918585836453226226001247148378) * 10 ^ 70 +
        0600242389803766443539345963635996059137320922863405739827177913203216) * 10 ^ 70 +
        3899919471079324333614381285815097893352548860100166528961625818343178) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_74 :
    recurrence5Scalar0Left.coeff 74 =
      (((((306 * 10 ^ 70 +
        8502096716975368745682108161324771101619370236202217058378832904889284) * 10 ^ 70 +
        4279570681438670969045491015133049919369554870541776533639313524566862) * 10 ^ 70 +
        8138087948502157900757217997194686475606591239249135947746202388829462) * 10 ^ 70 +
        1939930486003865695498090800223140969253577740719325731997396442735608) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_75 :
    recurrence5Scalar0Left.coeff 75 =
      -(((((2 * 10 ^ 70 +
        6115390173210868981961352052560998544252622103711683112922301939812056) * 10 ^ 70 +
        4573470498578347029895276101099696357621730303547042936376760961257200) * 10 ^ 70 +
        4474415541750203955728758960531149421617620311754836509298952115537016) * 10 ^ 70 +
        3711129600905042691850826399249278775346855906702134749200486792920572) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_76 :
    recurrence5Scalar0Left.coeff 76 =
      -(((((115383 * 10 ^ 70 +
        5672427570552454695980561326629976456423973552268268391604880913241238) * 10 ^ 70 +
        0992941011691886237282620850838276585898017420150336921766201872728352) * 10 ^ 70 +
        4522597747891782250553614384500836883890308019942092714860046110780729) * 10 ^ 70 +
        4143886182269287511907811291909703675027212895767273814975691000167572) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_77 :
    recurrence5Scalar0Left.coeff 77 =
      (((((4235390 * 10 ^ 70 +
        4756936098266810285498011213152794625045018871662017207693805552676660) * 10 ^ 70 +
        4622158052867101810946610616446195313705020893019797618085602976829123) * 10 ^ 70 +
        8358047527901518699026981292407223739836757469598202958383482385179943) * 10 ^ 70 +
        5327786681588607396933756752580613323963766466473594724252577456509636) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_78 :
    recurrence5Scalar0Left.coeff 78 =
      -(((((112414434 * 10 ^ 70 +
        3474144013302176375565360698941063645301738771710024629440642629362083) * 10 ^ 70 +
        1049160839473185473289048049548705521734679540691396429090458103497567) * 10 ^ 70 +
        7044671720652930194657767397799480384964173844789749259022155641003055) * 10 ^ 70 +
        8541599768825308077743747934592120209653906396064327084588341218945464) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_79 :
    recurrence5Scalar0Left.coeff 79 =
      (((((2558442503 * 10 ^ 70 +
        1576267339168011379307205223018916468278899351722358336757489505539144) * 10 ^ 70 +
        7448963223093542542672977571142478895319549221635002704907956272719928) * 10 ^ 70 +
        9258528281222132327686268918859504406360695663105101605201264250810189) * 10 ^ 70 +
        5829889912821926263788594801695966359470352946354178496060249870687834) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_80 :
    recurrence5Scalar0Left.coeff 80 =
      -(((((52685929526 * 10 ^ 70 +
        5939536676846717402173201559220626823837266295472235739573417059917627) * 10 ^ 70 +
        6214622675563798103239367783032106751041219768767208072796989094957096) * 10 ^ 70 +
        1692761994507316486436567420882317977193170136379255294376997979975594) * 10 ^ 70 +
        7668143925792948878559186439126557005756354502150056301351117941617146) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_81 :
    recurrence5Scalar0Left.coeff 81 =
      (((((1005736262211 * 10 ^ 70 +
        2975256815476024020997172704002874856017373931168421857232787926881549) * 10 ^ 70 +
        2698863976601171378567397835290280559140293051042225328473646033786414) * 10 ^ 70 +
        5035355267707442023904232849537009013382724885803631646263438082244773) * 10 ^ 70 +
        2935522195792130593309293114001307122924253043535181005471167472148290) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_82 :
    recurrence5Scalar0Left.coeff 82 =
      -(((((18031698050680 * 10 ^ 70 +
        0099898839999210683704105027326379430138249826041147366317236316004680) * 10 ^ 70 +
        7958049056851138183014669313801105041240242930193981059376397982041361) * 10 ^ 70 +
        3094064240357622582325231111634814205026409759585701658539237386861312) * 10 ^ 70 +
        1348340164996023093000608583682801038092851950847771783391402884903267) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_83 :
    recurrence5Scalar0Left.coeff 83 =
      (((((306072668423403 * 10 ^ 70 +
        5128246574106966238863793958845051052357257802063319042246385316780321) * 10 ^ 70 +
        9061323832150626830049630990559950663043680999073217894861340690795665) * 10 ^ 70 +
        9984394491458701041018197150853082367901216700215050113390060657704060) * 10 ^ 70 +
        8266466780748902092592441740394862650506453998750399821710836871204285) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_84 :
    recurrence5Scalar0Left.coeff 84 =
      -(((((4944826629142440 * 10 ^ 70 +
        9762785807359531896154066271610184249877161351955728158164657113970057) * 10 ^ 70 +
        2131345762243988280100614372908800641359080680028072036661154793827647) * 10 ^ 70 +
        5072283041403977381895095261359817442163498572496276415210512673352881) * 10 ^ 70 +
        2132906019572499623390290374269264483789849630626506963781829552207795) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_85 :
    recurrence5Scalar0Left.coeff 85 =
      (((((76320939788022832 * 10 ^ 70 +
        9736230432053136580372485026899636750263149906681543718878466452781331) * 10 ^ 70 +
        4207699189435223890241930579434893522181991738658184164444120013547487) * 10 ^ 70 +
        8389407384116953301182571902005727279493594967311732981462672202898684) * 10 ^ 70 +
        4331102460978970664399891057279422263693545191609081407697506132240057) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_86 :
    recurrence5Scalar0Left.coeff 86 =
      -(((((1128525617854152823 * 10 ^ 70 +
        6846646111780882971470201173872433296138633567729550683392566204288822) * 10 ^ 70 +
        3557889117510497112621446743588699610688933940334375344988907278217477) * 10 ^ 70 +
        3105085569317462026393745741827161632438506162909993478895668304238929) * 10 ^ 70 +
        5670755848373354634804546338085492794029869549074428866937990990675483) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_87 :
    recurrence5Scalar0Left.coeff 87 =
      (((((16020991713006682467 * 10 ^ 70 +
        0184552227669005848134346821704092844088729666930651447112428922504570) * 10 ^ 70 +
        1300084098006298192398795688073843695695050664512855779159612878709012) * 10 ^ 70 +
        2301780278968028789628346225072025804604907011171777717445157187089847) * 10 ^ 70 +
        4406810609742527954479089366531736407602316791355317130422745492748771) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_88 :
    recurrence5Scalar0Left.coeff 88 =
      -(((((218738762809860455414 * 10 ^ 70 +
        6970179081993743536121367350862519035393143979186007437770075156932853) * 10 ^ 70 +
        0206259652334323743586601168517808088546977945700498851202238893223015) * 10 ^ 70 +
        3741180092508429581020106823522838478258545715787718055194122541692539) * 10 ^ 70 +
        3193930613375022136357524873018206934871190015487456985274870666957215) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_89 :
    recurrence5Scalar0Left.coeff 89 =
      (((((2876312451889651298350 * 10 ^ 70 +
        2706960040701484789781472539394619736320401941883845928271217199962698) * 10 ^ 70 +
        4357588549558510921282251609895982914022389913513795362025611371873821) * 10 ^ 70 +
        2197584581317229604831587004017497818045680279510475190456155610730195) * 10 ^ 70 +
        0994487610181857335963757848665822700924688197368049907946366271346787) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_90 :
    recurrence5Scalar0Left.coeff 90 =
      -(((((36470276080154047968875 * 10 ^ 70 +
        8365811402723265620471398426213643193425000977763695631537472001814796) * 10 ^ 70 +
        7768335417069847884374235236269432717757850812395502630024739542246856) * 10 ^ 70 +
        2398657042788593019138244341654460339480090559338491196876204993204205) * 10 ^ 70 +
        9366336831468191455862534862519052278055785348804826991048222501382547) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_91 :
    recurrence5Scalar0Left.coeff 91 =
      (((((446355393110020201752635 * 10 ^ 70 +
        0369210375448510680179377000103259786364800501495274777438778484014709) * 10 ^ 70 +
        3946517116883074797866952093815855406817904809920069885141350997710904) * 10 ^ 70 +
        5325681935003072038310148567399571039112417106200830179983427133882398) * 10 ^ 70 +
        9391580255903806012625791979809082724151268289835252803766729772859618) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_92 :
    recurrence5Scalar0Left.coeff 92 =
      -(((((5277783206787948703061489 * 10 ^ 70 +
        6861187815739873059175454303023101571168779351608313929668103185359465) * 10 ^ 70 +
        3585589579218361508695929682098105661193969610361127194383927117052368) * 10 ^ 70 +
        3963424263173528881773486919463783756542631682369816396277083442136877) * 10 ^ 70 +
        0935701556869488051667386998343394375801852637585731096366658607516106) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_93 :
    recurrence5Scalar0Left.coeff 93 =
      (((((60338969624270499719793584 * 10 ^ 70 +
        2482578044460203236507223886342699921774065359118748281007572925083487) * 10 ^ 70 +
        0155524000808876779083149760930175998435482503922631146697754883619749) * 10 ^ 70 +
        2795323705927630033189461005979605262623815520437701657780975330709093) * 10 ^ 70 +
        5785922467662994356542666847871748110918760499494224545147598588552726) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_94 :
    recurrence5Scalar0Left.coeff 94 =
      -(((((667469573121262413835682193 * 10 ^ 70 +
        0200617315069550779772988985612738170089226523121163404950261118667674) * 10 ^ 70 +
        1378660646753869118083735646384391936206069908038740499397024851119223) * 10 ^ 70 +
        7747993679251058185692671872704067614597857417324840423372607539876088) * 10 ^ 70 +
        3064110083704965847856126123604049582430979634227349040759811476939756) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_95 :
    recurrence5Scalar0Left.coeff 95 =
      (((((7148840896160518135910539223 * 10 ^ 70 +
        3249101726684297149536776998159811798965203625392306351794063357417492) * 10 ^ 70 +
        2610988351375112523449152766479698324829412059418729639110709624777040) * 10 ^ 70 +
        6456399457400648013753690981781777615752118086490109174602705845777991) * 10 ^ 70 +
        7419787614621621548664316198528256559164768188584314486742996895940789) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_96 :
    recurrence5Scalar0Left.coeff 96 =
      -(((((74177187739313041001473024899 * 10 ^ 70 +
        6048372420114269340915743629944257998923170920655505151564017357951166) * 10 ^ 70 +
        8177029645824505822431340542040060553105480527563635831410033756894394) * 10 ^ 70 +
        6702346549921742287356818261040309952749090909569248073883117347199082) * 10 ^ 70 +
        4486689480808012139555639695920866007014557855462929731372395490862289) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_97 :
    recurrence5Scalar0Left.coeff 97 =
      (((((746064154675521241567300682061 * 10 ^ 70 +
        2639740083208684974708087665618777114372499802563402609793452961820171) * 10 ^ 70 +
        1501317312878148376717342289143773930016205957637220781499345278678329) * 10 ^ 70 +
        6546207738742408876421517458109771940356494377557826117084234216110157) * 10 ^ 70 +
        5286538364370156526270122025210343041554361581100943230627410661743664) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_98 :
    recurrence5Scalar0Left.coeff 98 =
      -(((((7277413855136267363472898793934 * 10 ^ 70 +
        5546030995531425739312683600333130545404595499866300302195937767407896) * 10 ^ 70 +
        6688186944809402055006807806234899038876023446847668372116880967669932) * 10 ^ 70 +
        3581356886137692594325427528391104957501216347006294768722987992576074) * 10 ^ 70 +
        7263968231041552657832261989078459007277935781402662095069631788414706) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_99 :
    recurrence5Scalar0Left.coeff 99 =
      (((((68878384387257700236928023086260 * 10 ^ 70 +
        1812996540345484970430717121638900105859482580471621002297707861119129) * 10 ^ 70 +
        0040363771556465002603757146023645025578817298309098318509209293253568) * 10 ^ 70 +
        0500813794477380479120694095234089230132578222053511785115142951883749) * 10 ^ 70 +
        5988199989209278739999410306566575724805160168318817629878682586956938) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_100 :
    recurrence5Scalar0Left.coeff 100 =
      -(((((632836445290416887998320673665410 * 10 ^ 70 +
        6189237666061026796210451135297612401074210433165403192605119672011017) * 10 ^ 70 +
        3511848245147181478053698480207239178859616822286553863420173587071693) * 10 ^ 70 +
        5022268587118660822376799619953286197888539616247192909297944887081518) * 10 ^ 70 +
        9150391593500380583332450598647754608957917823991235286616350161651307) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_101 :
    recurrence5Scalar0Left.coeff 101 =
      (((((5646634237169576411328450345518963 * 10 ^ 70 +
        5258604259325396400528522267570775978836939090481190359264382995388079) * 10 ^ 70 +
        5216675505158651528999746112376225535383184105589404282259708200223040) * 10 ^ 70 +
        5565503812083682013363648125109003879957388379692895133635429032671359) * 10 ^ 70 +
        3188887104874579607719362719599719806494819576331310624671679123424555) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_102 :
    recurrence5Scalar0Left.coeff 102 =
      -(((((48950264604287651225622555605746846 * 10 ^ 70 +
        9133257062298769004999950912338936823161341857017948356322297773986039) * 10 ^ 70 +
        8724024152907064422328524085733229006539873035211211512331632929861008) * 10 ^ 70 +
        8787263892882589772542022766376366403041632607389649241592336220746327) * 10 ^ 70 +
        2820439207742529180423104249087530526226058582611330695897973276496091) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_103 :
    recurrence5Scalar0Left.coeff 103 =
      (((((412436244196466546188529602293063094 * 10 ^ 70 +
        3244948920847631686535442043375682633561345507976096787101730654452038) * 10 ^ 70 +
        3577498296607231398993649849943505857345625747873017709752408259904702) * 10 ^ 70 +
        4628317058102920344666132671197489964190351137163893518669659222216311) * 10 ^ 70 +
        5720450230423684913508898934209298637615121671794914428308173031152131) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_104 :
    recurrence5Scalar0Left.coeff 104 =
      -(((((3378754616392855834365628077840903728 * 10 ^ 70 +
        5871335822901969630635812636192920808727134547654216553752057568556000) * 10 ^ 70 +
        5546437849121339902819999454441004425139650607510597281215447801481686) * 10 ^ 70 +
        6154387746088665922964655703677423777310012054812890251302667854509951) * 10 ^ 70 +
        1815575207397206948233636721615042607294937886526229306056284806160997) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_105 :
    recurrence5Scalar0Left.coeff 105 =
      (((((26922128013505016303309356181866422751 * 10 ^ 70 +
        3707539504607693288574101100649613522394814253393174826373481756033427) * 10 ^ 70 +
        8161929955666699095644700401985982901248023160972121613354676456393147) * 10 ^ 70 +
        6507706641336190437821527530315220620245177863412762720905722048050792) * 10 ^ 70 +
        8443896344848343440554860794299093838430326861632767826543003297957462) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_106 :
    recurrence5Scalar0Left.coeff 106 =
      -(((((208719817884942623829843497246202826056 * 10 ^ 70 +
        6945493367490144982717778227170108558482398845590059804143597313447643) * 10 ^ 70 +
        0748447001859018634226364669020007421478765137918773662005926211407881) * 10 ^ 70 +
        8209915574526793387172953706616471326809802241070287801251272744447384) * 10 ^ 70 +
        4019487344089474822235467617640687475466607098163751427812929499253384) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_107 :
    recurrence5Scalar0Left.coeff 107 =
      (((((1574934709146204610900422236147788217813 * 10 ^ 70 +
        7630852040708022214546211759353472436200115630970852138945166104661334) * 10 ^ 70 +
        1704799275246143638288043402184901956841121243201101003728151795594050) * 10 ^ 70 +
        0992229951098481388085962882158943744044837426128683784709694876068065) * 10 ^ 70 +
        9942532626974911830542515610405569733047201158151340367900728180080563) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_108 :
    recurrence5Scalar0Left.coeff 108 =
      -(((((11570277056984943671745471907424640521606 * 10 ^ 70 +
        9466202050558029079605752374751844210296951653523000936984628302529160) * 10 ^ 70 +
        8356505201925131266756526477123526659360822274727452550420038409850636) * 10 ^ 70 +
        9163878207528485132453882081987223769203034507571486924389395648744105) * 10 ^ 70 +
        3276547396369002873325725619382958305635550922611109348441945682139617) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_109 :
    recurrence5Scalar0Left.coeff 109 =
      (((((82782823157911531074615132894592530446109 * 10 ^ 70 +
        2932982389770265137007284747019971267141966518318712484416467651561202) * 10 ^ 70 +
        4112153945214833693876020970633004480072877939757867377817855017546383) * 10 ^ 70 +
        9115135848272249667734911037714543963793555982099900478814328202637753) * 10 ^ 70 +
        7697780557868110821345527167587895172062475026764482525421920142301980) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_110 :
    recurrence5Scalar0Left.coeff 110 =
      -(((((577006102806154788313475767922679972858055 * 10 ^ 70 +
        8781042636140435505646033396235204012289365091759769286533424008248150) * 10 ^ 70 +
        8417815404406386879437420506888988383764840055561241902419269290984246) * 10 ^ 70 +
        7293519427505228413026502686147119769259649932731876736575497396485791) * 10 ^ 70 +
        4128334729418499110361092332376991730479027149282279159216035916013719) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_111 :
    recurrence5Scalar0Left.coeff 111 =
      (((((3919119389664327265872293918076812897309486 * 10 ^ 70 +
        2755926834671168648376832141262294568029610495640606042555234779734622) * 10 ^ 70 +
        0796985578607170241599455933323336875272843767559007953597573214200493) * 10 ^ 70 +
        8656599749108846238249323532763713671823338853324249381909615823566859) * 10 ^ 70 +
        1326466942567853574635704513113333440980381977083071191134042363347849) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_112 :
    recurrence5Scalar0Left.coeff 112 =
      -(((((25946856636523092940125091389251581449880891 * 10 ^ 70 +
        9792061529162961526451621318774132997897749210830166319653986680746678) * 10 ^ 70 +
        7652074361545180010374417139243408444500976702719903668685538423220920) * 10 ^ 70 +
        3992992267849571995680027703178771277914971271380428472482259375912384) * 10 ^ 70 +
        7605786584346560970783107591850139753012218266928911069565692483685728) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_113 :
    recurrence5Scalar0Left.coeff 113 =
      (((((167488775742758254604251074583745564360595765 * 10 ^ 70 +
        0261267489206782153328032110999303643732589326845865473503627286210686) * 10 ^ 70 +
        2483714326403536610310009210462177405961429176849787358080015635917844) * 10 ^ 70 +
        0751142950468122334979421506728603629571173617690940960256371219875523) * 10 ^ 70 +
        4479368923961806070708256671737005165610371878541924027099289162174826) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_114 :
    recurrence5Scalar0Left.coeff 114 =
      -(((((1054397473760676349371580228763543912247605185 * 10 ^ 70 +
        8260804108375864409430560007216872904688269831590520936995576039889953) * 10 ^ 70 +
        1113986849807354437065309225915020137370743114830122017281094511589538) * 10 ^ 70 +
        1175867260567537152451670436099029115064001232183815854814468246966873) * 10 ^ 70 +
        6006327641795974136881724774958595401593477444247480660841521641114426) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_115 :
    recurrence5Scalar0Left.coeff 115 =
      (((((6475157576698074571621239399019288214334830501 * 10 ^ 70 +
        5490300463169211601543815454509902856371022827145753846635403974771872) * 10 ^ 70 +
        0086027317109562901292899759567396053504729884585145085147613114753892) * 10 ^ 70 +
        5103679637885087488788378243051097333552013890605504079189651798124551) * 10 ^ 70 +
        0162430192937229640151963780552608670920712374082911565164634329442641) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_116 :
    recurrence5Scalar0Left.coeff 116 =
      -(((((38799856154159466840421958550240043290743454919 * 10 ^ 70 +
        0447290751969380601101294653455677511068060969471990038830654717052860) * 10 ^ 70 +
        1046632185923644173111462888898850605715692711418110182574721267312439) * 10 ^ 70 +
        3114551663921270917240199846128793743385716539280253432911501597769441) * 10 ^ 70 +
        4555058131911511073820498904002292329577549703834938592538330925360585) : ℚ) := by
  unfold recurrence5Scalar0Left
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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Left_coeff_160 :
    recurrence5Scalar0Left.coeff 160 =
      -((((((27 * 10 ^ 70 +
        9256435916268325026954610241270203753886163035040538749389599116474827) * 10 ^ 70 +
        1845419209106087940898485429242099876143812612786805423008108095731971) * 10 ^ 70 +
        5380696373798182458869158526652441938863133843228354463805587484166011) * 10 ^ 70 +
        3569897821322798052052168836179075141345880022413563097399580772046495) * 10 ^ 70 +
        3266097820019181535665297596971482368120965396653309488972048400477396) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_161 :
    recurrence5Scalar0Left.coeff 161 =
      ((((((65 * 10 ^ 70 +
        8490817678370662643417203187444564208094283366116792070329935442309850) * 10 ^ 70 +
        7798400350936647485454845954972764280418990428184516312329805670434225) * 10 ^ 70 +
        3710996802142794683967934434213357444330985583773933844726909095828789) * 10 ^ 70 +
        2784666452875144939561377555995329727913445923260376342265068284142538) * 10 ^ 70 +
        0715812066279385078184312102928780191312619160849292216099621000822557) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_162 :
    recurrence5Scalar0Left.coeff 162 =
      -((((((152 * 10 ^ 70 +
        4770207273233064187272034457586360690376616677501080716695025035379058) * 10 ^ 70 +
        4914541086494091301823915470577313079152712624525430357152866562068203) * 10 ^ 70 +
        8053288551556692727367582632195268622429661815348698290954889473443384) * 10 ^ 70 +
        0276837774302493453009619809096618169613906926572101840291482537596046) * 10 ^ 70 +
        0301428175746053708504758508088672015406511636755285929173065997292539) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_163 :
    recurrence5Scalar0Left.coeff 163 =
      ((((((346 * 10 ^ 70 +
        7354136558329893995527433655735490150579331424060673364000860956994157) * 10 ^ 70 +
        0707514779433823047736742871403397668717526856751485379458674601867852) * 10 ^ 70 +
        6250328896162307242247976432835079233615084428542065157179496327772600) * 10 ^ 70 +
        4589056892852403831662996755310264968161270503481367866001862395547133) * 10 ^ 70 +
        8811287247263532415020828100770173414583911684628494148147108688757435) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_164 :
    recurrence5Scalar0Left.coeff 164 =
      -((((((774 * 10 ^ 70 +
        3928954218092254312113348938869821191286391753653798191329370134730820) * 10 ^ 70 +
        3685224309817745115421822957223550848584310506720634832961924979529357) * 10 ^ 70 +
        3968430626201080927085360067346867181531308525885209708819223047233129) * 10 ^ 70 +
        2312140025564333551535917144933374556891091012269477450247467330395629) * 10 ^ 70 +
        6444350379306668905478767428484009264192906946034619616441524190099930) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_165 :
    recurrence5Scalar0Left.coeff 165 =
      ((((((1698 * 10 ^ 70 +
        7261372893079743907971718210177275607212950488056503315514750890125050) * 10 ^ 70 +
        3176665934926720896485394438984655970732039178087040597278637056596066) * 10 ^ 70 +
        5197290868524675740602366334262361137055301171892359178968723734651217) * 10 ^ 70 +
        5587102350844988662261875093721171884683693605000871897081122868498228) * 10 ^ 70 +
        3493495727191772458233475477460642878841364490433429689164152397013949) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_166 :
    recurrence5Scalar0Left.coeff 166 =
      -((((((3660 * 10 ^ 70 +
        2690300317606695437730613670216013983820866816937566218462364779373194) * 10 ^ 70 +
        4397066609470289638931283458998550424371045659066191261382227101005027) * 10 ^ 70 +
        9058407355053782817648158677528275707012392627574649175605751622137888) * 10 ^ 70 +
        3669755918465064042287417874965189414209817981181721694755529353775125) * 10 ^ 70 +
        6912694342796961411268258137294370754045265296207952696083596893089723) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_167 :
    recurrence5Scalar0Left.coeff 167 =
      ((((((7747 * 10 ^ 70 +
        4425146849532979067289960313888518325930751531173384244888807447801166) * 10 ^ 70 +
        6844141068063468325106130858206755852327457010689555042941784109974486) * 10 ^ 70 +
        6433777158765710448464620283793478462110986486164180258103422133002739) * 10 ^ 70 +
        3434393808548672119637644778899302093561663681025314336353037170456117) * 10 ^ 70 +
        8112198805943302396368570274535711386290631927313356815224551427655354) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_168 :
    recurrence5Scalar0Left.coeff 168 =
      -((((((16109 * 10 ^ 70 +
        6777488662066189704868120638941662263085974397516971711841650865551856) * 10 ^ 70 +
        8744858065403361106481909553700444859690097399655510929924909055606621) * 10 ^ 70 +
        7712849748749162316070856518565839595458032399186377262707560889701565) * 10 ^ 70 +
        4771817253718545293851160794595049030240092730070596566305571466374339) * 10 ^ 70 +
        3753314877873941546111863009756693364487020189145831588754849847991044) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_169 :
    recurrence5Scalar0Left.coeff 169 =
      ((((((32909 * 10 ^ 70 +
        8004310717195773344790540301567203716863457488838691782429349153295561) * 10 ^ 70 +
        7008674109154545791470982367301084034710351054047673282060791950924411) * 10 ^ 70 +
        1374151149142687787430446781008128693849170113521806238202038244983224) * 10 ^ 70 +
        6824167894728882203681334187105545328870467828458652726464200377015521) * 10 ^ 70 +
        2159416706585755605626327679889802172391231649324859360673276522562768) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_170 :
    recurrence5Scalar0Left.coeff 170 =
      -((((((66054 * 10 ^ 70 +
        0866369315393936785820362270928280109369136629530801652574781143566819) * 10 ^ 70 +
        6463676147737899792735971225885973114083701682283031384115758074494904) * 10 ^ 70 +
        4299939642409958100619250279672760939723715096383044800440426122722857) * 10 ^ 70 +
        3313084291749585424542250888435226461456611597375154161134079042338777) * 10 ^ 70 +
        0357002559849664909672575395948986233294292662958545750227681576791558) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_171 :
    recurrence5Scalar0Left.coeff 171 =
      ((((((130267 * 10 ^ 70 +
        3918623904223718268473119441761040404756203633416485926767565173261116) * 10 ^ 70 +
        0469603628588695436666231736289197544345915153126349536268754271969271) * 10 ^ 70 +
        3048153027004725640312556139739317646699913762385882047577210531973042) * 10 ^ 70 +
        3368072530362391922364279926875926893071222121746236805334573839759035) * 10 ^ 70 +
        0003991516144233830512221174712589916385185051741181733749582128080737) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_172 :
    recurrence5Scalar0Left.coeff 172 =
      -((((((252440 * 10 ^ 70 +
        0617190749988244457925319682904571375628435399204041499800532255755239) * 10 ^ 70 +
        3555998537709668142053372749336066084711220506112289918890487256623003) * 10 ^ 70 +
        2490969571554695177458381196846806363632775384315776520543530269145630) * 10 ^ 70 +
        3283556982152572352954431801357861053646537336693044397181937046598500) * 10 ^ 70 +
        2231111498413956782565414342566633707912737815333758078257173857124650) : ℚ) := by
  unfold recurrence5Scalar0Left
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

theorem recurrence5Scalar0Left_coeff_173 :
    recurrence5Scalar0Left.coeff 173 =
      ((((((480719 * 10 ^ 70 +
        5179297815013599443009183523949866479340342341966440087041525394033158) * 10 ^ 70 +
        9580659348200011361154548718791744422513761887601746470890161893080762) * 10 ^ 70 +
        5464720612779443958848233201024059594211998131422940811086461696560337) * 10 ^ 70 +
        9681978848874356073422359996771938550936470344136007230302390284162519) * 10 ^ 70 +
        4847741181478975216895939600792552689357484160883549115033838263367561) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
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

theorem recurrence5Scalar0Left_coeff_174 :
    recurrence5Scalar0Left.coeff 174 =
      -((((((899621 * 10 ^ 70 +
        8427393574221280612015030270551023722412673688184437879169732902325212) * 10 ^ 70 +
        6738596435167988105521750864185533976903000722477048096723870941896918) * 10 ^ 70 +
        5678876059292963553690559167372929428469303360698482986560123880902813) * 10 ^ 70 +
        5568100451598876168972450398854889321392186215710709491657301360579769) * 10 ^ 70 +
        7720650877038362553272745392066437546124118133834757544135286873623357) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
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

theorem recurrence5Scalar0Left_coeff_175 :
    recurrence5Scalar0Left.coeff 175 =
      ((((((1654574 * 10 ^ 70 +
        4034236243002969264740098846496215649839397782925660147640263699015419) * 10 ^ 70 +
        8482606446149053848468874350272586206918322605497378654799706423858855) * 10 ^ 70 +
        6225210083553576229243774072477689719323229495802399386631835850917355) * 10 ^ 70 +
        3525785227680842782419324166914220221716795271584847065821320307877586) * 10 ^ 70 +
        6845501258738557346317510067566890567126461589022069187051902686277749) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
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

theorem recurrence5Scalar0Left_coeff_176 :
    recurrence5Scalar0Left.coeff 176 =
      -((((((2990842 * 10 ^ 70 +
        1787648586444358885895025883569391208316405382386703853168079889314192) * 10 ^ 70 +
        8372999916837632456174349095676738950693759951984027827196153460776207) * 10 ^ 70 +
        5611203377499678964280411994443187696594730564636878223558929720555162) * 10 ^ 70 +
        0236846859455439541901080295743942433097483444593095227342730979245179) * 10 ^ 70 +
        2914426812679628299457445929570063665437541439842648381183673697488642) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 0 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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

private theorem recurrence5Scalar0Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_177 :
    recurrence5Scalar0Left.coeff 177 =
      ((((((5313784 * 10 ^ 70 +
        1005486223396617024223966003340571588227105217192461628147207572371858) * 10 ^ 70 +
        3274005258938827140300460260484529820224962722553149401279951758889307) * 10 ^ 70 +
        7230714875615731868756200872237192702301536335162906486233220557778433) * 10 ^ 70 +
        5248227219067326373761517128047333762641242098707645104623148505925314) * 10 ^ 70 +
        0202531584763720249348465813107074430564232384610512031972679288789081) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 1 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_178 :
    recurrence5Scalar0Left.coeff 178 =
      -((((((9279816 * 10 ^ 70 +
        5367273282859114188132010892208780763772179411840571409004933630707380) * 10 ^ 70 +
        1450778628284480502875037781324338030651965271016837317454604472593686) * 10 ^ 70 +
        8285473437478189550386862169795474717758104132281635528531433151238720) * 10 ^ 70 +
        0637314649912346149903041754350187427173637914680321635168179566597768) * 10 ^ 70 +
        3782058923841292760783913325241237214380818811491328211014300623013628) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 2 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_179 :
    recurrence5Scalar0Left.coeff 179 =
      ((((((15930205 * 10 ^ 70 +
        2984257867871301820793593658396239656430527982437009393264604319039826) * 10 ^ 70 +
        7149587438903504719050419665934204030393162396230325822962839685028476) * 10 ^ 70 +
        2878647458694002761784339765646845591620036480654522764874302034854761) * 10 ^ 70 +
        6441683920126464247428298872715156339219347674165199451129629729284567) * 10 ^ 70 +
        3902611626880887849997543923402950561516131932192392023946745680307641) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 3 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_180 :
    recurrence5Scalar0Left.coeff 180 =
      -((((((26882573 * 10 ^ 70 +
        9670580273823311560901179990713778381082503640325554743320575647333473) * 10 ^ 70 +
        9666927830093796162379708366639423055552819591627883858781046424786557) * 10 ^ 70 +
        1835400957326443224632060998755084498391460097998489308210028250979949) * 10 ^ 70 +
        4256720233239946715678226271171275455202817348923652876467238944994567) * 10 ^ 70 +
        6157451355626679300406710333581980938544738611600873968824225871874315) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 4 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_181 :
    recurrence5Scalar0Left.coeff 181 =
      ((((((44597284 * 10 ^ 70 +
        3083696381827960814972713699167991983999063718204691655175289732572611) * 10 ^ 70 +
        5521150250075069914749726635805384964914292143452545503403265487305778) * 10 ^ 70 +
        7953157290094967949330608232611435879249046074821722297860542494813610) * 10 ^ 70 +
        4589975177710090931103728215456813926862589789725606876125255467666580) * 10 ^ 70 +
        8249293554895570490115484142671571460400579242242662499953914701709298) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 5 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_182 :
    recurrence5Scalar0Left.coeff 182 =
      -((((((72736814 * 10 ^ 70 +
        2228294059312424613333299689158206394147113593987818995930849816964295) * 10 ^ 70 +
        5275382086910615100308945486902056960839175823772272827667459394410165) * 10 ^ 70 +
        8999926388628190222419620611426751903440655859723200381000076182932515) * 10 ^ 70 +
        8362378384922741139085774780841808434719561352140426143034035847759555) * 10 ^ 70 +
        8395245709990871678712720552687432376472161153621690730409567739706172) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 6 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_183 :
    recurrence5Scalar0Left.coeff 183 =
      ((((((116634835 * 10 ^ 70 +
        5159197844713549335739630892176852719872815770973450845075551596531431) * 10 ^ 70 +
        7466013624124064636582057434356580756899199071546743311765786887612826) * 10 ^ 70 +
        7465672413790008278182652629361257648119413903844366475123973894355215) * 10 ^ 70 +
        2967179951217905268785278883743489964228761658265176486684227355312763) * 10 ^ 70 +
        9216516652038889092138030779130376534912933188365733507431735398865640) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 7 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_184 :
    recurrence5Scalar0Left.coeff 184 =
      -((((((183886536 * 10 ^ 70 +
        3811502761022160030586517922612550794501018897290174867520036508192940) * 10 ^ 70 +
        2714048561699748387984830718960521779324080999152804186030683558657184) * 10 ^ 70 +
        0531092499198669146412337074514609793284348082528117153830950542766704) * 10 ^ 70 +
        4709779276096005436481421209228421301309697905870511920097708195978563) * 10 ^ 70 +
        7753851413810241040058957901159564069433918401924088312097042953663898) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 8 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_185 :
    recurrence5Scalar0Left.coeff 185 =
      ((((((285061395 * 10 ^ 70 +
        6098211343282854776518734756326593205007767469402838912981045060659778) * 10 ^ 70 +
        8690504633252921700138919033587377172988132470120962963460468384271516) * 10 ^ 70 +
        7110469221726160603748309937134922412121863703362018940298673933242528) * 10 ^ 70 +
        7702794347403856640270733169086409632803376672645165290672029135143835) * 10 ^ 70 +
        3638520102052682737000119051855084518553571984035105383531599979172341) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 9 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_186 :
    recurrence5Scalar0Left.coeff 186 =
      -((((((434522806 * 10 ^ 70 +
        0422012257484097590196308854969507295294135575039923076957069958814326) * 10 ^ 70 +
        2475682464839892131846898636060287725432464489863580341764288126702781) * 10 ^ 70 +
        0485705179412700038855789425907515269843210045725768680385255194099835) * 10 ^ 70 +
        5096244412169192372603911439472878320220059418825719227974875914677364) * 10 ^ 70 +
        5734953120045282207579392161379110326874543772294900281145342331618249) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 10 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_187 :
    recurrence5Scalar0Left.coeff 187 =
      ((((((651314911 * 10 ^ 70 +
        5233021695010597907988655825685342021401392412840980401648702630141931) * 10 ^ 70 +
        3304800794797407296950138323194877134760603834988179779428484305199166) * 10 ^ 70 +
        3219056983846057287509951030538494898857026149198958643891855392359188) * 10 ^ 70 +
        3838276400814863734711083106667222268348954253034813951978362939725092) * 10 ^ 70 +
        4292022468896979158168158445892195478580030029121887143701381382243481) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 11 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_188 :
    recurrence5Scalar0Left.coeff 188 =
      -((((((960046033 * 10 ^ 70 +
        4545341549125048649079983152259549078486235748867139123241556029669216) * 10 ^ 70 +
        7156773533765847686881434025774425017884160576595923259027234591120914) * 10 ^ 70 +
        0444455676938734362451828937980773606384851066219065315606622652594867) * 10 ^ 70 +
        3085701385026185108245011518632554710575495182859428817507988921582526) * 10 ^ 70 +
        1347332974521178827680752709260126823257681003305099901613452834728873) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 12 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_189 :
    recurrence5Scalar0Left.coeff 189 =
      ((((((1391661921 * 10 ^ 70 +
        3235437154225544789841082002227960091572655401121305903309955026686225) * 10 ^ 70 +
        1240368322485932509531565795059515360334287542915251389403221314325950) * 10 ^ 70 +
        8345193952951454981471230023185247020716155276313685233247477941175381) * 10 ^ 70 +
        8905359652941488669826849697875224943783267026378503758939164338256677) * 10 ^ 70 +
        2671885089527928178499261632656131035591892804050712239093354542383312) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 13 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_190 :
    recurrence5Scalar0Left.coeff 190 =
      -((((((1983964526 * 10 ^ 70 +
        1990300726232092435656087586299330169249292620524289803920868146614246) * 10 ^ 70 +
        3189287281556871190497650095102466359103437914818977740566498210810161) * 10 ^ 70 +
        1568802519367056009801350661691066956922880517309601060835310264374092) * 10 ^ 70 +
        3393570175681482737393213265756249253041761989842589864380314610936890) * 10 ^ 70 +
        1146902902882062784931859535457909451733954300607709806641680911450948) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 14 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_191 :
    recurrence5Scalar0Left.coeff 191 =
      ((((((2781698971 * 10 ^ 70 +
        8504613170442549155257005170040626927003567624504169259570127813664605) * 10 ^ 70 +
        2377019387060822115892784237004243003306144304335576893459443617519405) * 10 ^ 70 +
        7639207144545495719280381581726717883742389755358320506572682892322946) * 10 ^ 70 +
        8640874708278915683250506366362826477389899778315727555432115066669792) * 10 ^ 70 +
        4731273907585240900630499853377825964263319867315535552140452803785668) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 15 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_192 :
    recurrence5Scalar0Left.coeff 192 =
      -((((((3836010713 * 10 ^ 70 +
        9857179727563449193655529133576778163663719052193921931955992193432341) * 10 ^ 70 +
        1347673959907462511776445273514891287989729388980100187194635267350908) * 10 ^ 70 +
        7138608871134655545399215046792680041878120015907440195307741869189081) * 10 ^ 70 +
        5553444956286684073178676820695302376210659252369746001516194808367592) * 10 ^ 70 +
        8750695628691432041180852180139664602528934715538458479732553315019546) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 16 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_193 :
    recurrence5Scalar0Left.coeff 193 =
      ((((((5203075520 * 10 ^ 70 +
        3229869158114676316499570700399155553112000490092499903740428032854879) * 10 ^ 70 +
        0355024855286209730591421416579227168170946808069165763259784980493438) * 10 ^ 70 +
        6669579423766704431738733966552780940871004109876594433194819642776144) * 10 ^ 70 +
        8602136445976627855641928678331027786914530860878955988495492041043302) * 10 ^ 70 +
        2273057808053731655019298893490606017622157774329868839300012669255840) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 17 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_194 :
    recurrence5Scalar0Left.coeff 194 =
      -((((((6941735643 * 10 ^ 70 +
        8744476730558164506298741410980271845402305394518433467412490527465486) * 10 ^ 70 +
        8687277217266041326774890416535551326815516132948370032088970652229055) * 10 ^ 70 +
        3467369027496378448229557076898353963946694459623023901889764415423405) * 10 ^ 70 +
        3996633038996696750469955811159957733963874943973087495683114032681666) * 10 ^ 70 +
        4372411156580969106683005412684878321237240610159032564959249549823070) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 18 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_195 :
    recurrence5Scalar0Left.coeff 195 =
      ((((((9110043053 * 10 ^ 70 +
        0682204196325404065046352212059932753467849704818064734271990483543953) * 10 ^ 70 +
        2010877173530404633945963127157388526684267905364167515878195225420331) * 10 ^ 70 +
        1997455572892707871454002698721400218500650841438488716026719737216255) * 10 ^ 70 +
        8710534366932749405585411628844229482816175258879557061071520906351999) * 10 ^ 70 +
        9853334492906186396011998018216462591591899411847547922101617530742712) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 19 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_196 :
    recurrence5Scalar0Left.coeff 196 =
      -((((((11760717177 * 10 ^ 70 +
        2135878046271185946037850288100320051353838525756093105977338473823706) * 10 ^ 70 +
        1568001125776727356272656706932653265569553146986117073395382252573409) * 10 ^ 70 +
        1828234047194644023847324478256453151128355546943948678726935946127537) * 10 ^ 70 +
        9499305511932619117703676789758224053288349531829711832755582416695558) * 10 ^ 70 +
        7135968627466928546036169672504763076467732063957459872887210568700866) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 20 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_197 :
    recurrence5Scalar0Left.coeff 197 =
      ((((((14935666321 * 10 ^ 70 +
        7959815456902471537999349087859288763952126388485989587944358852789054) * 10 ^ 70 +
        8626144126334797294329864578631552484170052934861020548095799257520000) * 10 ^ 70 +
        3497829090702225786726376794167227710337681656283593797487771131911583) * 10 ^ 70 +
        8299281910164524214578153074271312283841701517424187099326331517243779) * 10 ^ 70 +
        3056144843047201878755001565003150791530621936709320856891392682630815) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 21 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_198 :
    recurrence5Scalar0Left.coeff 198 =
      -((((((18659886965 * 10 ^ 70 +
        0211724192436622560670516024262778221270093312876422693210987785407271) * 10 ^ 70 +
        9687094799351272257718755282633354886928302496710743523825269775546278) * 10 ^ 70 +
        8726556018913509917447702323958487806684205489084352356935693108557901) * 10 ^ 70 +
        9256403420841556635204103800990232402339053321425887958850345940372768) * 10 ^ 70 +
        8964391261714941463910854188268467172657641195820708619761062413383905) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 22 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_199 :
    recurrence5Scalar0Left.coeff 199 =
      ((((((22935223927 * 10 ^ 70 +
        1494614876618691695243561570313383599210861357953763175000996237235294) * 10 ^ 70 +
        6610559208339229382352282356290994107647303701447656170154474300058051) * 10 ^ 70 +
        5648814977236905837888165295464610503644911397528140424668704753686710) * 10 ^ 70 +
        4342743380095676319352544154416747328624386924527906181611688205681656) * 10 ^ 70 +
        5139650733312199102226803249844849887603755774165658337783640088035902) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 23 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_200 :
    recurrence5Scalar0Left.coeff 200 =
      -((((((27734620861 * 10 ^ 70 +
        8439273704825239587005531508848325307915392949226027274910643156564006) * 10 ^ 70 +
        8705849084986148313817469177439769364203369230639197142483965079571300) * 10 ^ 70 +
        0921051229494229526382433677689164688733530881438318189639112715792754) * 10 ^ 70 +
        5390821985499349665276583394454448364924501912386267970009033978521437) * 10 ^ 70 +
        2649747898927491954962395336768362428124056995765801856887760337922840) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 24 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_201 :
    recurrence5Scalar0Left.coeff 201 =
      ((((((32997585485 * 10 ^ 70 +
        4302359328641358793499029366252043773032628957520324413146461957804106) * 10 ^ 70 +
        0625799808357166592184882187123815634019168386378379504641771914274523) * 10 ^ 70 +
        1333972184502866284971048879829275846972969919033911743363025297454699) * 10 ^ 70 +
        2539415946510284647297683895361502736860235081896994194083521950464067) * 10 ^ 70 +
        0131830741399568285628521957648554331426854795580201504581756674103901) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 25 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_202 :
    recurrence5Scalar0Left.coeff 202 =
      -((((((38627609967 * 10 ^ 70 +
        3347474621926277492867051207289626165554354840814987208370888309157276) * 10 ^ 70 +
        4370964932345819373639854686465320419102668465665035776131462273407163) * 10 ^ 70 +
        6604466246018719082227538417554879713125133228922652033864314197408583) * 10 ^ 70 +
        5177319407071373300130247863852855728283258415911782131447705609374603) * 10 ^ 70 +
        7073555291444134432948515219523731688012982216925156623953958776581160) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 26 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_203 :
    recurrence5Scalar0Left.coeff 203 =
      ((((((44492203845 * 10 ^ 70 +
        2851507673667232974070110094013098578942048615994584986081783798972686) * 10 ^ 70 +
        8017011910053790464358868151349918537178161613479989736592373329146310) * 10 ^ 70 +
        6965433611930571049386802900335635571363832947549444986827446692987402) * 10 ^ 70 +
        2254628744145294255801761392822943772155488834889512654240506472369769) * 10 ^ 70 +
        2707038993171487599949936916893610336116728005108022860572630106505398) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 27 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_204 :
    recurrence5Scalar0Left.coeff 204 =
      -((((((50426007377 * 10 ^ 70 +
        2045765329765582558748982378219445052298661886259783107621909987727652) * 10 ^ 70 +
        1195264705989964597597717956374674370106697263168234999321801611574784) * 10 ^ 70 +
        7061440403432116353670118356682998739073565873633330565283729519187225) * 10 ^ 70 +
        9386798694354208615531275639375822487619343694386664486046877538355852) * 10 ^ 70 +
        2328285678744816577902030772185378425916749189197074868773436306326162) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 28 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_205 :
    recurrence5Scalar0Left.coeff 205 =
      ((((((56237166782 * 10 ^ 70 +
        1074324331562988761827207666576100894179999424488437905072318135426185) * 10 ^ 70 +
        5573296561224643042161937974023313993593516046318019037697730072692637) * 10 ^ 70 +
        1682178800664291296376350534024051256846128474034402858757663246860659) * 10 ^ 70 +
        3398120694693308664348570788565944777314178447944760956368585613871756) * 10 ^ 70 +
        9005427153129033577199932267640749124813256802323812291533812883103663) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 29 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_206 :
    recurrence5Scalar0Left.coeff 206 =
      -((((((61716796718 * 10 ^ 70 +
        7749794586608532458475888342775844543995717947951910394601322959818081) * 10 ^ 70 +
        6345856486293768063107870161134167087485261628667679616589599839349292) * 10 ^ 70 +
        8924065093567198262009999821702180648898063961880147403569379795988285) * 10 ^ 70 +
        7797539922335414092484694534252138691171556071293840204924756581881648) * 10 ^ 70 +
        2045573903088725793547277719354056121205365886662948006558277995249414) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 30 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_207 :
    recurrence5Scalar0Left.coeff 207 =
      ((((((66650972816 * 10 ^ 70 +
        9279922038128126517666349725520832774445735283020226119830630979517086) * 10 ^ 70 +
        3978150042339922434514538333131187413206578306146524798750793836643199) * 10 ^ 70 +
        7989685767058250920183302432742257671574311529561290451769691432310643) * 10 ^ 70 +
        9208392542863180538324984559130528773694981600809363906213658741913362) * 10 ^ 70 +
        1018883642178104948031976727879335502829077712569554410556694105039931) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 31 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_208 :
    recurrence5Scalar0Left.coeff 208 =
      -((((((70834341564 * 10 ^ 70 +
        6232366476165067535968792698798679468977135687251575434218052502675204) * 10 ^ 70 +
        9758668768843868291472121842839473528720192843880111532708204934248974) * 10 ^ 70 +
        2845692835291433077291692391784622631275539267636077768685932886116070) * 10 ^ 70 +
        1919838492700479977483348631923513131218748811251137696671110590644954) * 10 ^ 70 +
        6098013784384458210776064617974463498585960802754084939166066008672676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 32 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_209 :
    recurrence5Scalar0Left.coeff 209 =
      ((((((74084161690 * 10 ^ 70 +
        6895706532353617113889939828671706706377932536628745198041442786245728) * 10 ^ 70 +
        8365742579488720551440431087497743225505449125335942750980173894691166) * 10 ^ 70 +
        7341079400752994443756096854699416060192385712284546674324807317017798) * 10 ^ 70 +
        9065071393293592266233075897690285052150572886358051002186226317096876) * 10 ^ 70 +
        5554538484536608978367734733937045264030418379709283298435407771824385) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 33 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_210 :
    recurrence5Scalar0Left.coeff 210 =
      -((((((76253447863 * 10 ^ 70 +
        3982752654783230900001001325629355589453225649497087808858406638471474) * 10 ^ 70 +
        9743792688486231728202664053794408394813558383784550329347196635179216) * 10 ^ 70 +
        3929010088470814709841972330810691735407125084602310567135335749332757) * 10 ^ 70 +
        8341200516792118908513260078215786080003554820552117492670287426017869) * 10 ^ 70 +
        4263499241807812805493941619549615135238699381190804367859057040977676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 34 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_211 :
    recurrence5Scalar0Left.coeff 211 =
      ((((((77241904624 * 10 ^ 70 +
        2834804838043131651072025333169821240288235266233761318885085124851104) * 10 ^ 70 +
        9566575818166949750017848023764903250681405921480441740158800638718794) * 10 ^ 70 +
        2210529465958986066864604491784124350628707042713351103268492590983415) * 10 ^ 70 +
        5242329863308509369691737481252630544596190461393992591993458781946465) * 10 ^ 70 +
        1918786652241679309218437340864091318328710221221922159570679672523678) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 35 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_212 :
    recurrence5Scalar0Left.coeff 212 =
      -((((((77003523038 * 10 ^ 70 +
        8705553017792570064357307391095464785233350408687545448942554985937615) * 10 ^ 70 +
        1460934334202648061557893073629363406917446409359866994178354316656399) * 10 ^ 70 +
        1160752656805953111184187265905135647574550194384717333087614580895549) * 10 ^ 70 +
        5613427733654993223125321919892543988595518419029353385534667128844078) * 10 ^ 70 +
        8739994694684027723640537488607400966140056126716140983531012761234746) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 36 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_213 :
    recurrence5Scalar0Left.coeff 213 =
      ((((((75550045577 * 10 ^ 70 +
        6430507260122912281190333019079410633122900121003702412024687141382539) * 10 ^ 70 +
        2079053746014520682016800897499239079971342092870185613394770125151530) * 10 ^ 70 +
        8669838947345609784228476750226700863864106939902043180025928699925715) * 10 ^ 70 +
        6650934217042080410821337473159904090942306371332973455248072915612316) * 10 ^ 70 +
        8884741108929105439355844393068420036428720929922926053204015743512863) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 37 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_214 :
    recurrence5Scalar0Left.coeff 214 =
      -((((((72949943453 * 10 ^ 70 +
        5939576249526072106447159112248277978510779199516185312638864514695102) * 10 ^ 70 +
        4688718406494643003064786000057374221856661139106925381913346873703201) * 10 ^ 70 +
        6725489067630430733325702574090404898436204825213739892038253631144388) * 10 ^ 70 +
        9740183047970439174335621013846833624643411170753824999391844992793497) * 10 ^ 70 +
        1190922396077831987745473549279709320488369448023460058030994557052013) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 38 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_215 :
    recurrence5Scalar0Left.coeff 215 =
      ((((((69323035209 * 10 ^ 70 +
        2307611170601081769306835177361605157521458904903262712376704559829928) * 10 ^ 70 +
        8811347421164128981399563077234367363159754381112962715352607737142850) * 10 ^ 70 +
        6599614975951538996311250118358899443157168237846890600825656671712771) * 10 ^ 70 +
        9176393685292492117042520502182400528486004809493528748440568463980663) * 10 ^ 70 +
        0154370089145131306002058298067355148229891322664648104110201724776993) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 39 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_216 :
    recurrence5Scalar0Left.coeff 216 =
      -((((((64831338875 * 10 ^ 70 +
        2667639461836342054431156570246796872908732815785633123319826633520493) * 10 ^ 70 +
        3567684462702842573288498719273306289829999592359606481629654381373980) * 10 ^ 70 +
        0588052035285658844001873383666099345436932968821069149075855413056689) * 10 ^ 70 +
        5854582420020063161625025112998232148272535395484328203935386604667256) * 10 ^ 70 +
        9809356283386630017916861015046610063260851704964597820329627120560073) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 40 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_217 :
    recurrence5Scalar0Left.coeff 217 =
      ((((((59667129797 * 10 ^ 70 +
        8968541769121682615997422694957236329625780080497562548978948061502332) * 10 ^ 70 +
        1404947239797324692001726516082693432979824147121992398205973712713708) * 10 ^ 70 +
        0171983964307525242375086193865796471467927248927837188198444127200060) * 10 ^ 70 +
        9747168398935224713046972378931743287342873611953585406689362791519680) * 10 ^ 70 +
        2712979739245274819040192036143481200832704679140612317378892622382250) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 41 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_218 :
    recurrence5Scalar0Left.coeff 218 =
      -((((((54039423978 * 10 ^ 70 +
        3652133073554579165688498645873680532294522974599047486823944715617318) * 10 ^ 70 +
        2987781734374725260711031123751550263044704734360012839842457276379901) * 10 ^ 70 +
        3326490480852849358901487942132926315476509589629342101067503218998941) * 10 ^ 70 +
        3775558777264665402170647793804885165941376336634802874288946427953292) * 10 ^ 70 +
        6875946110826495898856863989231468025384872179128936310376889218260194) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 42 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_219 :
    recurrence5Scalar0Left.coeff 219 =
      ((((((48160195995 * 10 ^ 70 +
        6303698398734809105423085779405669692172428606288334223118754025856156) * 10 ^ 70 +
        2480083171317558788008221550349708808763389697163631745267034565925577) * 10 ^ 70 +
        8126469666263487310337289504680297210543459061013601533988760329454944) * 10 ^ 70 +
        3771171800939357968347002419058823872220409495691699849943883559510340) * 10 ^ 70 +
        0699332824353198926302051455355780656299046924782295363915451402930080) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 43 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_220 :
    recurrence5Scalar0Left.coeff 220 =
      -((((((42231569697 * 10 ^ 70 +
        5274533972935411898496770384636082020190833421296462537130175152761054) * 10 ^ 70 +
        4315962777557141457879489998210255385293808250136994130275326886478231) * 10 ^ 70 +
        6453345717901519077842622436274299716431202415561873006124898019560711) * 10 ^ 70 +
        6243691072739360423491514912836573079410930088043295736476507568726936) * 10 ^ 70 +
        2302630229507912408660384174696486837580298176197601778058889690370792) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 44 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_221 :
    recurrence5Scalar0Left.coeff 221 =
      ((((((36435010704 * 10 ^ 70 +
        5087515206348462125585633151666264762658562261290713544183622953553581) * 10 ^ 70 +
        5608609058977815741737156000770243072931998266094340415347653066898234) * 10 ^ 70 +
        0876726405331233588122247655294192095776296385491366200898239993578698) * 10 ^ 70 +
        4752747369906144158356167308840634843141527837386892001444430945465594) * 10 ^ 70 +
        1414344832815337135065819554170512435737456254270302339806497457898335) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 45 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_222 :
    recurrence5Scalar0Left.coeff 222 =
      -((((((30923242267 * 10 ^ 70 +
        7653526160625891280412906313957388399339606161079373695055017824295107) * 10 ^ 70 +
        7902002304432359361170790577319494654243807223070339165586690970383762) * 10 ^ 70 +
        7086409745613946880447808976248558083552777824207599588417725267259945) * 10 ^ 70 +
        9478019924300744333751503978507951862600351406036707847232863830822042) * 10 ^ 70 +
        8762789965872750871643393532315436309483772657246249843231161588021460) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 46 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_223 :
    recurrence5Scalar0Left.coeff 223 =
      ((((((25815250076 * 10 ^ 70 +
        6963473957531659573989379877134712240212918980634055865469331264865521) * 10 ^ 70 +
        1403158856414211053953323907870693035557116488737447463714567677778712) * 10 ^ 70 +
        1343038176846423012620155741736766828160342050669078007059502555595925) * 10 ^ 70 +
        4689364639275875265480393903723477767406577938632777226719754269817387) * 10 ^ 70 +
        3729352142108638166983071964733045604533295772427115261976571162111381) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 47 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
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
  rw [recurrence5Scalar0Left_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
