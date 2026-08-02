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

private theorem recurrence5Scalar0Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_224 :
    recurrence5Scalar0Left.coeff 224 =
      -((((((21194388279 * 10 ^ 70 +
        5971452267019933478810436307246209337850385966471609529768729670380563) * 10 ^ 70 +
        6925864187471270918628783647269539185104094186636572495830656838417274) * 10 ^ 70 +
        3704893299012911438081030985803852809182288564633067288299635324929286) * 10 ^ 70 +
        0630735445029139765229947550436310989150981842372137020145842010694245) * 10 ^ 70 +
        9947076407596864647742510503594936896970709097576453484843136343710877) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 48 +
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
  rw [recurrence5Scalar0Left_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_225 :
    recurrence5Scalar0Left.coeff 225 =
      ((((((17109292455 * 10 ^ 70 +
        2047681851942215431389940506113066785848977767753171825373123734564756) * 10 ^ 70 +
        1442418165646795850952658035295902916063718050245786226297946168860804) * 10 ^ 70 +
        2727905909284373928644952018889828429862983144485601313543328953305291) * 10 ^ 70 +
        0057441803793026803748463688162049194550480631673116986872115394445423) * 10 ^ 70 +
        4506518093644902416510893999414611657846340849465170186510599101654453) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 49 +
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
  rw [recurrence5Scalar0Left_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_226 :
    recurrence5Scalar0Left.coeff 226 =
      -((((((13577077057 * 10 ^ 70 +
        9615938275458576709251328813169355302327403487237853887333469180322409) * 10 ^ 70 +
        3070112446015872680131867558664071938493359799808547442436417237868291) * 10 ^ 70 +
        8856942875618071629295987366279677988756863926776719439481347339160856) * 10 ^ 70 +
        7648076827941256658218998274293987685362019768886283028997324391826894) * 10 ^ 70 +
        8823835474603582899588143729591859693817016682192691742769647267096672) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 50 +
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
  rw [recurrence5Scalar0Left_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_227 :
    recurrence5Scalar0Left.coeff 227 =
      ((((((10588160904 * 10 ^ 70 +
        0450365710000082502970384753655068304137523203008198428825024343241166) * 10 ^ 70 +
        6828907679446931121634487110829885674464533253758938753408452020838485) * 10 ^ 70 +
        2663442335976535010288978442778614530244550742881727545462298620783306) * 10 ^ 70 +
        8297664410884466483964043653923781119212636639281123102955935359323717) * 10 ^ 70 +
        6881359283420638626946878320562105533806394627276336928327980820420976) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 51 +
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
  rw [recurrence5Scalar0Left_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_228 :
    recurrence5Scalar0Left.coeff 228 =
      -((((((8112025074 * 10 ^ 70 +
        4142114838147658855806677602168472908978497497014888356107250816870315) * 10 ^ 70 +
        0407508207727153952557776812344994003629672243007024855597600174212620) * 10 ^ 70 +
        0267463412202803690534582965904392897035106395137024645916957637566262) * 10 ^ 70 +
        7739911558348911294378209499809180044146865772452169844437266549931478) * 10 ^ 70 +
        1478918599686324399809537397256788678080808476805727532301011218964748) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 52 +
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
  rw [recurrence5Scalar0Left_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_229 :
    recurrence5Scalar0Left.coeff 229 =
      ((((((6103250844 * 10 ^ 70 +
        2537346298208027312267427899637057174572174133101215053353767998818378) * 10 ^ 70 +
        0640371219023040520420411305305579325963463972474301696369235893680830) * 10 ^ 70 +
        0068577705438241311931759238362049261745861169068828919929999798678793) * 10 ^ 70 +
        0943124568278512419791132754934824011653864168728940193200061628200307) * 10 ^ 70 +
        5920610262972327422809044137532940402768617920106817876712342205511770) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 53 +
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
  rw [recurrence5Scalar0Left_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_230 :
    recurrence5Scalar0Left.coeff 230 =
      -((((((4507289896 * 10 ^ 70 +
        6862143452100657254369888916136434230193177278846688000211890672148663) * 10 ^ 70 +
        6589810879812677521252557729821486333396365359138154378766328300031666) * 10 ^ 70 +
        4430469182310243033839917344718009135952934703364434237534427828487305) * 10 ^ 70 +
        7046139518900013304420202007435722015468562993328273493546612194102827) * 10 ^ 70 +
        0737655567610607009433225587285314492264051090829478161294161583992040) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 54 +
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
  rw [recurrence5Scalar0Left_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_231 :
    recurrence5Scalar0Left.coeff 231 =
      ((((((3265560212 * 10 ^ 70 +
        7594483913334161247983264115069985630979953602432787518188645609409028) * 10 ^ 70 +
        1584364761716543238561788970701427414660457445158381847928226400176046) * 10 ^ 70 +
        9812341746559496711619585212459062979961708188641051434913209641544571) * 10 ^ 70 +
        5780060636481834228641759900797900674066662105439055399917976601299937) * 10 ^ 70 +
        3620950064969569192284318903672242794788508436256538988280339240985843) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 55 +
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
  rw [recurrence5Scalar0Left_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_232 :
    recurrence5Scalar0Left.coeff 232 =
      -((((((2319614191 * 10 ^ 70 +
        0997896540148709267990969199464238579262175462061319427787925173254485) * 10 ^ 70 +
        9455778200115761835195646710900142854112532345663940464851944545771608) * 10 ^ 70 +
        7076840023236399840307744888693580561724393638957062286674894164095370) * 10 ^ 70 +
        1060955964848840945261156286362597527716702649012168688325719464143099) * 10 ^ 70 +
        4090576791152433986051916626618226445921843458147029772089034531554729) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 56 +
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
  rw [recurrence5Scalar0Left_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_233 :
    recurrence5Scalar0Left.coeff 233 =
      ((((((1614270127 * 10 ^ 70 +
        6345852333057629592366998945589481473506518656542744868730705676605108) * 10 ^ 70 +
        6533220904099424924400936119889389711821305613951956309720067219465132) * 10 ^ 70 +
        8891576731402625720684092103870056503167563539931143985795022569398937) * 10 ^ 70 +
        8921879366682242512709023344321891390418152515568520991041283926697333) * 10 ^ 70 +
        0850013201434286328750827756944019440265053628751048102733940581708475) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 57 +
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
  rw [recurrence5Scalar0Left_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_234 :
    recurrence5Scalar0Left.coeff 234 =
      -((((((1099719437 * 10 ^ 70 +
        5608021943491290309396081961283157362886984161173895178797824668835586) * 10 ^ 70 +
        2036348092458575639422382444931309037182464629099301037954589562750881) * 10 ^ 70 +
        2279949160125240518550410894130107211246579516024179837395459612852294) * 10 ^ 70 +
        3758739142617419218000111809263689288683716392958665596721078326950787) * 10 ^ 70 +
        3724016722092359307946185475446705483889644783846936436224271809473681) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 58 +
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
  rw [recurrence5Scalar0Left_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_235 :
    recurrence5Scalar0Left.coeff 235 =
      ((((((732711713 * 10 ^ 70 +
        3684648955865666606926566339621773778770234545099087077132806574798155) * 10 ^ 70 +
        2742450329487336247412776331168007187511902841214795093836380152980909) * 10 ^ 70 +
        3430518226881038789005241759532116591670471578189320279236067061262396) * 10 ^ 70 +
        0611918393231599748872499484790179397132223639277851076529558978683097) * 10 ^ 70 +
        7767441548465281833998460604674587108461350517956693555106247022066497) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 59 +
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
  rw [recurrence5Scalar0Left_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_236 :
    recurrence5Scalar0Left.coeff 236 =
      -((((((476975708 * 10 ^ 70 +
        5315121146828029946615703170101811895142581281033757074555554712389827) * 10 ^ 70 +
        9007537296283544371808292757622262558921245955551805003553161281892525) * 10 ^ 70 +
        1254164963352263711912614139978240886329357337230950560457902521296189) * 10 ^ 70 +
        0101601226396351613117562673559567876796464235133171573943562328364195) * 10 ^ 70 +
        4716987611498308912242084192635565716818693581138205131285954501258878) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 60 +
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
  rw [recurrence5Scalar0Left_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_237 :
    recurrence5Scalar0Left.coeff 237 =
      ((((((303059219 * 10 ^ 70 +
        0852774907233458118785908370774899780122758424629963839727418619618747) * 10 ^ 70 +
        3084170752260818237437585270815077195421703525567585053981347271162482) * 10 ^ 70 +
        7128975903021725754670941854723518262964028660034283764261639521865115) * 10 ^ 70 +
        2103177682295501050110528543473023978908189380083631562897150895227669) * 10 ^ 70 +
        6265846785451942783134513156347227445695875365851367389948898830821476) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 61 +
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
  rw [recurrence5Scalar0Left_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_238 :
    recurrence5Scalar0Left.coeff 238 =
      -((((((187770354 * 10 ^ 70 +
        9794659437803239309315357374368078710054682054174183005199718273038478) * 10 ^ 70 +
        1970505111378256634557773515382487332374263106652428047370280908750126) * 10 ^ 70 +
        9714704673793615933177544303056836391198751373905488310991019459555156) * 10 ^ 70 +
        6393169899838650460864047153237383094391735380908021235384134068413140) * 10 ^ 70 +
        1203720394265836668903594603438393604048110273372169206907065796750333) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 62 +
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
  rw [recurrence5Scalar0Left_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_239 :
    recurrence5Scalar0Left.coeff 239 =
      ((((((113384104 * 10 ^ 70 +
        8963657720721423143068384873878876434474915707259820568512379066019581) * 10 ^ 70 +
        6936648617111511181342371849199561275281334330731683347614357858629280) * 10 ^ 70 +
        3745244161753110634775357618897655787130345457784634185404047109730613) * 10 ^ 70 +
        5232944927918860266262392607494272219765751218405060651559371539245971) * 10 ^ 70 +
        1084947934850947149616725950817842698316621052146410801901338269510299) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 63 +
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
  rw [recurrence5Scalar0Left_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_240 :
    recurrence5Scalar0Left.coeff 240 =
      -((((((66748766 * 10 ^ 70 +
        7400887088895358171476418880463191310394529546039408188738778603679457) * 10 ^ 70 +
        7408121682751324410610403685957249233838360474310356026427153934915855) * 10 ^ 70 +
        4777964985076025452386461007756868159449602067933188001322661431941434) * 10 ^ 70 +
        7980480076368903111957047589759680235861163364477653676250409118326454) * 10 ^ 70 +
        6580260963509360316996793398142188130401034266462199874181545829582236) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 64 +
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
  rw [recurrence5Scalar0Left_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_241 :
    recurrence5Scalar0Left.coeff 241 =
      ((((((38393211 * 10 ^ 70 +
        3170976925416237783693152759810601916386728663703657713790184162217930) * 10 ^ 70 +
        0586099320743983546849914839560218098941306483174395376609492927795068) * 10 ^ 70 +
        1164619493913423863867841738138838616033624647560454093437122503820433) * 10 ^ 70 +
        5878570531209609400350552011918360533001974162229207894539794510489490) * 10 ^ 70 +
        3204669374720640049560123556891734205154114902932912880875038973130036) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 65 +
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
  rw [recurrence5Scalar0Left_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_242 :
    recurrence5Scalar0Left.coeff 242 =
      -((((((21703068 * 10 ^ 70 +
        5636322434784809587330616919897861766960726406276127458319483350944268) * 10 ^ 70 +
        2923142695922637268097534016798560582654767389125940783603193594690417) * 10 ^ 70 +
        8421217237490101859220133081399266936810415361179895540720429089537479) * 10 ^ 70 +
        5148729101867609421939387919262846194124225529419878235581373789007050) * 10 ^ 70 +
        0435084972218224681449577872116122363471640385208487043998107483959568) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 66 +
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
  rw [recurrence5Scalar0Left_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_243 :
    recurrence5Scalar0Left.coeff 243 =
      ((((((12205111 * 10 ^ 70 +
        7898549610057798984436020777820488573894355651008507933037250564394207) * 10 ^ 70 +
        3781960067122489049307549844944661920620545223603708630262747096122558) * 10 ^ 70 +
        6685007036181179405298564998127852344284047032958043553511126523834115) * 10 ^ 70 +
        3914970812861994832965499009033322030431554546617883964391971215682170) * 10 ^ 70 +
        5083040278160344515928386142561733573695495021795758651675479721029418) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 67 +
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
  rw [recurrence5Scalar0Left_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_244 :
    recurrence5Scalar0Left.coeff 244 =
      -((((((6976142 * 10 ^ 70 +
        2924222510697794024177101802989073615013060794989417249059349011477067) * 10 ^ 70 +
        3780195213511963730212643586632599239650103165997085419988841404825742) * 10 ^ 70 +
        4193594183431217414989053970244652061427206283742390546401803681267383) * 10 ^ 70 +
        0449231036728492336097907457644280384884664168458071278022509625674508) * 10 ^ 70 +
        5363053000371891688164803144574490884796628488064912962261268421311611) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 68 +
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
  rw [recurrence5Scalar0Left_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_245 :
    recurrence5Scalar0Left.coeff 245 =
      ((((((4176043 * 10 ^ 70 +
        5046149641564741049822667641967996256583746269284519867668489139557594) * 10 ^ 70 +
        5425128228438024052383102294108172929535891271219814123415166628420960) * 10 ^ 70 +
        6288137282365650140217802381265480826810615485010844597460269684472723) * 10 ^ 70 +
        2071637817153215597619114751730188543222807629299251067320988348186872) * 10 ^ 70 +
        1114780095926601031993716778269403479709683027435674953007951905959390) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 69 +
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
  rw [recurrence5Scalar0Left_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_246 :
    recurrence5Scalar0Left.coeff 246 =
      -((((((2693967 * 10 ^ 70 +
        4361009830193464049612715870749756505044920866855859392547765219407946) * 10 ^ 70 +
        3655167404113705251916063358900677180697267441024641739720013896573517) * 10 ^ 70 +
        2424612334779804128502712721926428773789617111386860322225404852191598) * 10 ^ 70 +
        8694802888506848604511136545389252939517702943344980435343341865418950) * 10 ^ 70 +
        4423719234739044858867792629565867038551889334233251482323389163019257) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 70 +
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
  rw [recurrence5Scalar0Left_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_247 :
    recurrence5Scalar0Left.coeff 247 =
      ((((((1890876 * 10 ^ 70 +
        3606359035432960611835591391980015564742667323200397132078108603799997) * 10 ^ 70 +
        4536934887371485751145026700577929072623589190980647528111155962512843) * 10 ^ 70 +
        3795678255554945329199843199980670145498486881098497015667449725882295) * 10 ^ 70 +
        3432353027041103905683155157522195470675865469181122504345549548144037) * 10 ^ 70 +
        2052998432610160104486639069023719069006007509444410614580574451100050) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 71 +
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
  rw [recurrence5Scalar0Left_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_248 :
    recurrence5Scalar0Left.coeff 248 =
      -((((((1419695 * 10 ^ 70 +
        0414509557005592739093570743034689277923409621815579510693292011750249) * 10 ^ 70 +
        1183335401396740124770895789494542892286078083650278928306924858313701) * 10 ^ 70 +
        9858564656193178612810620359560461629666385106422199769112659743982744) * 10 ^ 70 +
        6583931141707610740504667851309669028268033742422797689043128759439653) * 10 ^ 70 +
        5011827721838214787631104413505868306028096975080250991877807953730791) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 72 +
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
  rw [recurrence5Scalar0Left_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_249 :
    recurrence5Scalar0Left.coeff 249 =
      ((((((1104937 * 10 ^ 70 +
        7626165349866161272530974789809890297415351662293029969402971010747849) * 10 ^ 70 +
        3260761171811387363903273272856629852183558434407907642499610036022754) * 10 ^ 70 +
        2911408946094855526262330428550264508473758423345174588118602581003140) * 10 ^ 70 +
        9824278374249709244459811407287684629906864078763593571463761165040812) * 10 ^ 70 +
        4385019423807996986440539624462279522692961257901131649856781692003295) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 73 +
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
  rw [recurrence5Scalar0Left_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_250 :
    recurrence5Scalar0Left.coeff 250 =
      -((((((865812 * 10 ^ 70 +
        7471485186881146559754551170152876011574195955854284866633342122351467) * 10 ^ 70 +
        8518116395814057204758537700466757799108929548611836279439366728090827) * 10 ^ 70 +
        0433113672142125986848567001163730428031449654282323383401843139245714) * 10 ^ 70 +
        7906002332190066543092650924051089036562608461929789027089560943972378) * 10 ^ 70 +
        7732531668771610821422607376261206899097531247894893092140623829398855) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 74 +
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
  rw [recurrence5Scalar0Left_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_251 :
    recurrence5Scalar0Left.coeff 251 =
      ((((((669649 * 10 ^ 70 +
        5140374409091287409996675856789235309071694203914745922115431161040260) * 10 ^ 70 +
        4424512155067175429639728622336116734599276779649601040425448807675871) * 10 ^ 70 +
        9620188227746083177142016750439590068157960497795529391502425533992599) * 10 ^ 70 +
        9703828864845321810631402999769281038757954425581152316138446337559054) * 10 ^ 70 +
        3852415535524466479947570345889851681192180712559124218762357432885523) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 75 +
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
  rw [recurrence5Scalar0Left_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_252 :
    recurrence5Scalar0Left.coeff 252 =
      -((((((505457 * 10 ^ 70 +
        3667130052725903040637385082965404628444262648605211435949796751547784) * 10 ^ 70 +
        8552797121303395390878866564562284082783496226724238105717830090696961) * 10 ^ 70 +
        2893433283562010648322169324870558704835890529274047743285409508148267) * 10 ^ 70 +
        3419644266491152528132833087258664315091399889480057287334248822988369) * 10 ^ 70 +
        7823380565993206436486215908223482878082880237813423604414397729498734) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 76 +
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
  rw [recurrence5Scalar0Left_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_253 :
    recurrence5Scalar0Left.coeff 253 =
      ((((((370139 * 10 ^ 70 +
        1652471856852693798443044894641595221215140481539720962435727780292616) * 10 ^ 70 +
        7854589237333883406134482460084177311352580266639290981327306303120528) * 10 ^ 70 +
        4090464975253056513722237092241509510128610052589471858333072539381833) * 10 ^ 70 +
        2630052601685324786176339150696744835521491455446834704230703906107950) * 10 ^ 70 +
        2642518951803222346505775935654533882283829905194210191676597598891907) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 77 +
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
  rw [recurrence5Scalar0Left_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_254 :
    recurrence5Scalar0Left.coeff 254 =
      -((((((262164 * 10 ^ 70 +
        5663379398730640561745697809108594245349249170128857214117478317836871) * 10 ^ 70 +
        9966485416324373618699742881527608877839216162457127194608313150532831) * 10 ^ 70 +
        5497730311486022784272837643472193413125842096162147229816615089783774) * 10 ^ 70 +
        9017426932021646485895625124429702578993246862530208014147897128138507) * 10 ^ 70 +
        0146801589226070866117236073844318600474630308379279418220754626030098) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 78 +
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
  rw [recurrence5Scalar0Left_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_255 :
    recurrence5Scalar0Left.coeff 255 =
      ((((((179290 * 10 ^ 70 +
        6285234186319212331644183599113287009874694891091777800004350471475587) * 10 ^ 70 +
        6986463356548760936412541148335617119424745201945953317231317172943565) * 10 ^ 70 +
        7163436585532951019791238583327611010705605309525701208761905660522820) * 10 ^ 70 +
        1159830562383222487362840540052283208978519728828189122503566285678529) * 10 ^ 70 +
        9123141222397493867961292750716218954581595196641644398238211512006862) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 79 +
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
  rw [recurrence5Scalar0Left_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_256 :
    recurrence5Scalar0Left.coeff 256 =
      -((((((118227 * 10 ^ 70 +
        9293887218114822403782199290070432546057099632676418803259740840634104) * 10 ^ 70 +
        0422249002733123886803596259266087870915723757577272303200762272541661) * 10 ^ 70 +
        2567012412343000906984301266863796773577522024737709533383897939073243) * 10 ^ 70 +
        3097819611118484804381553740473030964019330061100216894869890414361292) * 10 ^ 70 +
        3767950078011048332816297344023578352807408453443972841990740029465125) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 80 +
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
  rw [recurrence5Scalar0Left_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_257 :
    recurrence5Scalar0Left.coeff 257 =
      ((((((75055 * 10 ^ 70 +
        4670251455684450705201734089853549759292994996224799138542699388142396) * 10 ^ 70 +
        9168937962233987211914529861728330820664712228868080334413304347833789) * 10 ^ 70 +
        0601726166804794596095012676532440456183886888221272448932695651234143) * 10 ^ 70 +
        1700585648601807060624759874547156840957951203236264076561606025190417) * 10 ^ 70 +
        7883809803464001561183844705564336187601240541229979634835939341531916) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 81 +
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
  rw [recurrence5Scalar0Left_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_258 :
    recurrence5Scalar0Left.coeff 258 =
      -((((((45773 * 10 ^ 70 +
        5097607399588154437074548326237502216871151622520278697267646842430821) * 10 ^ 70 +
        2477958480016035970037482502092255145334824685388186109510525583523402) * 10 ^ 70 +
        7389614375973316014318032405686306324335262387990079474633594534160237) * 10 ^ 70 +
        2896236881897079640644412221376530749115756334585750858182678917372643) * 10 ^ 70 +
        1969806645254036241936200476298171361546089694566346403872632649689290) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 82 +
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
  rw [recurrence5Scalar0Left_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_259 :
    recurrence5Scalar0Left.coeff 259 =
      ((((((26735 * 10 ^ 70 +
        2856471317148893747129576739656469273298420124504984895302627832211497) * 10 ^ 70 +
        0485301161966138345825428568212816559957589331424287679280318969489262) * 10 ^ 70 +
        6662239392100577817227928297284286268780694191987372333121669052671866) * 10 ^ 70 +
        4497073950777837156008653951781578620236076217084545119060238514055653) * 10 ^ 70 +
        6681682165233486761291289666986849228906226606003186827140182825184560) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 83 +
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
  rw [recurrence5Scalar0Left_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_260 :
    recurrence5Scalar0Left.coeff 260 =
      -((((((14889 * 10 ^ 70 +
        8873615235625595271295347711492663021383335219792109509775532306632102) * 10 ^ 70 +
        4232777172169011621518711448097639830401431320258460495540907148969112) * 10 ^ 70 +
        3565057791365112023381150776108338438855777663996195860544182687384323) * 10 ^ 70 +
        6682755685871316708318454216568775295661467203016883356162581643590727) * 10 ^ 70 +
        8883790687029973502699496023651966855135826075798429177987337718012243) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 84 +
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
  rw [recurrence5Scalar0Left_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_261 :
    recurrence5Scalar0Left.coeff 261 =
      ((((((7858 * 10 ^ 70 +
        4638282048411422251864727433867045905124939932700599584435705718895217) * 10 ^ 70 +
        2883800964824103792746789716673676150722001724176568435428898998442346) * 10 ^ 70 +
        9033947259048068557180512197347411525401564477538217934599627318298825) * 10 ^ 70 +
        0976631623168895182407194698246251864942549243980252436990466418217140) * 10 ^ 70 +
        8763380264031984580695153069499770661001312169770714842265752644548361) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 85 +
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
  rw [recurrence5Scalar0Left_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_262 :
    recurrence5Scalar0Left.coeff 262 =
      -((((((3896 * 10 ^ 70 +
        3339380885774535414514763968484930623850080363314153648112720677442664) * 10 ^ 70 +
        2253626987704346338959949528178478082898161817962984661255570917900831) * 10 ^ 70 +
        2547917289784654072033116266762430723754667677746951527809946070321213) * 10 ^ 70 +
        0798204268608670101937854015055232896837084445715740045145520854393535) * 10 ^ 70 +
        5322784636840540615449070805839398628007450788517978646401309643022677) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 86 +
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
  rw [recurrence5Scalar0Left_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_263 :
    recurrence5Scalar0Left.coeff 263 =
      ((((((1793 * 10 ^ 70 +
        8858746911195616368650491140219125494083609969768899881814482329610151) * 10 ^ 70 +
        3467833938204563726209227352021903079802815529567748281921321927189046) * 10 ^ 70 +
        8438883492110764224442362882217006010651800270980444883998965323710629) * 10 ^ 70 +
        8897012482916242261609288036555123702730686347650378401162080133450645) * 10 ^ 70 +
        4100323907815145108075186865298864322956029603620347938716291107674017) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 87 +
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
  rw [recurrence5Scalar0Left_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_264 :
    recurrence5Scalar0Left.coeff 264 =
      -((((((756 * 10 ^ 70 +
        8668629510095466036488199192114545684961015214722465806734098334197471) * 10 ^ 70 +
        3249079058163512397845527861940289346867391786348113672476052265610565) * 10 ^ 70 +
        5147290505681449477834693694375988614644963778214561243768061536917013) * 10 ^ 70 +
        9778597939790484355909069727341071708784436725001922258734058114274489) * 10 ^ 70 +
        1524130361449037389829206914606271633204979600542870594225335060483315) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 88 +
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
  rw [recurrence5Scalar0Left_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_265 :
    recurrence5Scalar0Left.coeff 265 =
      ((((((291 * 10 ^ 70 +
        8615501478875420293850483209510668795141566545834059591450628239149009) * 10 ^ 70 +
        5778164390042333641080204643861942992847103099498068343252168050796314) * 10 ^ 70 +
        1147235001132968600059209918023065151778493049390841649929335405473413) * 10 ^ 70 +
        2347384519576978347027361039597466019812430566848708197465210064570191) * 10 ^ 70 +
        2543921784311852044430914969698075919348971895573270517855858476227861) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 89 +
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
  rw [recurrence5Scalar0Left_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_266 :
    recurrence5Scalar0Left.coeff 266 =
      -((((((110 * 10 ^ 70 +
        1014837619526433938294870616740683259383985635769899880495450490638472) * 10 ^ 70 +
        6144806152381810807392711128387313129764857229643200127593533988412217) * 10 ^ 70 +
        0036795727289643997305432178191244653929093858574242978527851820047058) * 10 ^ 70 +
        1372244419883581962840467131760620715701703712117935841902599394571076) * 10 ^ 70 +
        7410185112257153918098228197987442591052200229530825443929814473628269) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 90 +
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
  rw [recurrence5Scalar0Left_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_267 :
    recurrence5Scalar0Left.coeff 267 =
      ((((((53 * 10 ^ 70 +
        7953031545927640036490473293802326887722744628113290296799693716468269) * 10 ^ 70 +
        3318840265305457807212227180260852250764539900483107563902608578546128) * 10 ^ 70 +
        0216212380467586531427214896075532642615104044721461721393632970379330) * 10 ^ 70 +
        1493273413146994380951754885126230434226273167480614469326007579493791) * 10 ^ 70 +
        2591435177317267137613936995237400470693803074999984547403834204014676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 91 +
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
  rw [recurrence5Scalar0Left_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_268 :
    recurrence5Scalar0Left.coeff 268 =
      -((((((43 * 10 ^ 70 +
        8142060538813355395526930114579534842789098745231829296866850818073036) * 10 ^ 70 +
        6667373405992428670028522107446147174106235887078220323217777292562104) * 10 ^ 70 +
        1754769749487079841652792724862871099322307216593712688267079337734807) * 10 ^ 70 +
        4015629981084706362991341475424837983446687855073953994440616183940144) * 10 ^ 70 +
        8470392996950497902916136021366247450168977592079418999307791379036409) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 92 +
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
  rw [recurrence5Scalar0Left_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_269 :
    recurrence5Scalar0Left.coeff 269 =
      ((((((45 * 10 ^ 70 +
        0098485731183975186899638457934898332430337963498070894031549652324745) * 10 ^ 70 +
        0613856217836531182366063879236225163262488619894411631085153537716615) * 10 ^ 70 +
        8516735630095703006342171186474561649744022318154445353308378370255124) * 10 ^ 70 +
        0413211451189453805345310345115559171611723076129476557959560483990648) * 10 ^ 70 +
        1455137443484428577220100721278704570749161371408208629829542799586950) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 93 +
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
  rw [recurrence5Scalar0Left_coeff_269_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_270 :
    recurrence5Scalar0Left.coeff 270 =
      -((((((44 * 10 ^ 70 +
        7412638611866857863932512296621457825416814615127870668983634291717345) * 10 ^ 70 +
        8419329621357011014374957770182657471971898742994267539498123515210087) * 10 ^ 70 +
        5510866673919404602015354087376859354220556108955178958727835015267012) * 10 ^ 70 +
        3341366306235124145836989963158246972999856510092434293774685519912562) * 10 ^ 70 +
        5074435669206124145755261772881631490015436854649196928178567343471834) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 94 +
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
  rw [recurrence5Scalar0Left_coeff_270_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_271 :
    recurrence5Scalar0Left.coeff 271 =
      ((((((40 * 10 ^ 70 +
        5326890015108088907752806271938125748063956452357006235940996306710847) * 10 ^ 70 +
        9680647878918209602468025027876702271991157970572367606875046029308894) * 10 ^ 70 +
        8424991257345854466857446772672074270720977371269942527764564566200255) * 10 ^ 70 +
        6099781156815163302311555621194471205265696719689791797657914577699279) * 10 ^ 70 +
        7266627251356905065342543532816496850027368814361359007617612156630766) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 95 +
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
  rw [recurrence5Scalar0Left_coeff_271_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_272 :
    recurrence5Scalar0Left.coeff 272 =
      -((((((33 * 10 ^ 70 +
        5876267088634082811868529333776791142872715956619483340434510827761025) * 10 ^ 70 +
        3530505580612168487965872812031139149334434624734850763871297638279196) * 10 ^ 70 +
        4008651933371019623090284316058379965164737600787193850570245543167363) * 10 ^ 70 +
        2974022486880836677811743821675903366881166045313376103799506963570635) * 10 ^ 70 +
        3267825261392876206770534722268385888994715223028874450308125173815458) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 96 +
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
  rw [recurrence5Scalar0Left_coeff_272_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_273 :
    recurrence5Scalar0Left.coeff 273 =
      ((((((25 * 10 ^ 70 +
        7781545546553326232671046542938512942239458418233322111344365121413299) * 10 ^ 70 +
        4853816452938490239728357685526954343778303135728650467881587060321118) * 10 ^ 70 +
        3650103113398830245348613514466319252940782976228080541567514977599228) * 10 ^ 70 +
        5180259629736942595909187307232602258469916614788583953509632487113604) * 10 ^ 70 +
        3223129231286026254881590035761410592673937069492622880048715940016145) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 97 +
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
  rw [recurrence5Scalar0Left_coeff_273_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_274 :
    recurrence5Scalar0Left.coeff 274 =
      -((((((18 * 10 ^ 70 +
        5187772700063623124788544222053977180165653721783832421106166538929304) * 10 ^ 70 +
        1398618688802516111766687330231195925969645797082743947824331092191865) * 10 ^ 70 +
        1788383556842833211044041846344245438346380277658485929196991935055744) * 10 ^ 70 +
        8615111474298734667454460524954777921260965295628009368485037548406354) * 10 ^ 70 +
        3111569874340988606263796846958641947451417856501827502949219674469909) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 98 +
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
  rw [recurrence5Scalar0Left_coeff_274_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_275 :
    recurrence5Scalar0Left.coeff 275 =
      ((((((12 * 10 ^ 70 +
        5461385827676474967838382165226098135342447674805512870171854403037716) * 10 ^ 70 +
        6320103667037007573288582384506262981125412267439708827564769029091725) * 10 ^ 70 +
        5230901172627886204166581602685057025165453702677226337470585869396221) * 10 ^ 70 +
        7752530484647723120829014435469249644981095135389519502232953501848723) * 10 ^ 70 +
        7019516706065921531088402350116604503428632964121373259531730688026396) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 99 +
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
  rw [recurrence5Scalar0Left_coeff_275_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_276 :
    recurrence5Scalar0Left.coeff 276 =
      -((((((8 * 10 ^ 70 +
        0548088975671711888922370558972268638368664193227756963033557957715281) * 10 ^ 70 +
        8976802281487308550960808528749327310633722730546815346844410567353576) * 10 ^ 70 +
        1890904535775879410282143688064461624138568042933762617853067209173441) * 10 ^ 70 +
        7978812361875099421606190942661951415928701039279663033245840730588207) * 10 ^ 70 +
        7496753411332417284930909475910516606128232282407936383074655817026193) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 100 +
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
  rw [recurrence5Scalar0Left_coeff_276_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_277 :
    recurrence5Scalar0Left.coeff 277 =
      ((((((4 * 10 ^ 70 +
        9141830828064446533461634572789792748173758069059966641414460228269617) * 10 ^ 70 +
        2312757105021259655159063721102742326063616259312623530408125375895896) * 10 ^ 70 +
        6026053331669160554013753661309255795166500315683261273076644603112384) * 10 ^ 70 +
        2834340215115392307835071210435009166826738028793186637112291331250957) * 10 ^ 70 +
        1363002970356348372047990698457430900592523288496651608394867063510861) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 101 +
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
  rw [recurrence5Scalar0Left_coeff_277_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_278 :
    recurrence5Scalar0Left.coeff 278 =
      -((((((2 * 10 ^ 70 +
        8519870910224581485004311307882688405827771017803928195652903795339388) * 10 ^ 70 +
        1294893389581933584071904684005489307207874952339717850950673709811354) * 10 ^ 70 +
        1332282391335544450963503725625159480027777232038068140337684306630608) * 10 ^ 70 +
        1448506016088218220337265593952411412043510204020547752933749024079508) * 10 ^ 70 +
        2415533223549245470559281178702195034019636375836838967489183263471217) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 102 +
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
  rw [recurrence5Scalar0Left_coeff_278_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_279 :
    recurrence5Scalar0Left.coeff 279 =
      ((((((1 * 10 ^ 70 +
        5736365264936419093146544828962276128676604254837350950145040250825887) * 10 ^ 70 +
        6876945576069656505774709547289439509384179811840323111699786542083798) * 10 ^ 70 +
        7552615293556951645416926341699386998363917332613874651536439496693941) * 10 ^ 70 +
        6707397156967328248873848808142769939846239353476545285746321391207052) * 10 ^ 70 +
        6938235943261258262261149812420486633865130600307077357803563989747628) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 103 +
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
  rw [recurrence5Scalar0Left_coeff_279_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_280 :
    recurrence5Scalar0Left.coeff 280 =
      -(((((8237187250203090421175627178674061963589779432811377864511839634296216 * 10 ^ 70 +
        0836865102283404828740631428196471918154879347507050141758064052961767) * 10 ^ 70 +
        1840561059194014110168983592649010186605911081024336253408860060202673) * 10 ^ 70 +
        0560996473467546057527469807299068562116542675827127344840478161873155) * 10 ^ 70 +
        3748583664746711511582346929890876704828571372508750776432236065818454) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 104 +
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
  rw [recurrence5Scalar0Left_coeff_280_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_281 :
    recurrence5Scalar0Left.coeff 281 =
      (((((4074093517570532202312926565328734947281105883755687017385371120170278 * 10 ^ 70 +
        9806758945233282861227048429957098338409140229806981563673055158632745) * 10 ^ 70 +
        2499420985075338305503469793113432513062925433975388607235356607515483) * 10 ^ 70 +
        7290295649086439342699878806849239273132430797790814027255688802339826) * 10 ^ 70 +
        6974648927069040497620601934956993419455842008156422340068514453945207) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 105 +
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
  rw [recurrence5Scalar0Left_coeff_281_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_282 :
    recurrence5Scalar0Left.coeff 282 =
      -(((((1892157534458732982475818973931960779516488923591476816118673928530939 * 10 ^ 70 +
        6980848982681867776162421408192051415556122628058210005708178401090208) * 10 ^ 70 +
        6802182170638635849186996879510716975057631366808424704281612555507574) * 10 ^ 70 +
        9746450024828373767049279510197387214715801922958543661847489247495689) * 10 ^ 70 +
        7191143817123252842069615083399568352736461189948608521313907725937362) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 106 +
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
  rw [recurrence5Scalar0Left_coeff_282_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_283 :
    recurrence5Scalar0Left.coeff 283 =
      (((((817931248770373204683822588869244943221751524107711202659955563260482 * 10 ^ 70 +
        3840547491188289559302999413945974484655537005235043496641613959019313) * 10 ^ 70 +
        0956760427344299886098241940830730595711960120446504944105173358105408) * 10 ^ 70 +
        8122670526651949016072680198809332398905043318493440797184012067566064) * 10 ^ 70 +
        1028078160053472784047925076682556864092530083444622989142619796647232) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 107 +
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
  rw [recurrence5Scalar0Left_coeff_283_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_284 :
    recurrence5Scalar0Left.coeff 284 =
      -(((((325471689944215270414781256028833856992032969011623530998836850495279 * 10 ^ 70 +
        0749441264247665035259151904670647839532759493287992374900158511661020) * 10 ^ 70 +
        6487735413304923154229582828359243284166059824499877257692195215512711) * 10 ^ 70 +
        1621611925210601093180243147452777466991614855743233828768862349157965) * 10 ^ 70 +
        6767635995967415785786027436213687647472212034147516244982647671281610) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 108 +
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
  rw [recurrence5Scalar0Left_coeff_284_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_285 :
    recurrence5Scalar0Left.coeff 285 =
      (((((118278745403984360486228899365400275505316815631332497096621383195945 * 10 ^ 70 +
        7860312064093565007780328605653396219381472012668482892106609170046245) * 10 ^ 70 +
        1528210574468730758650023109456937962023718408456798637663096315396555) * 10 ^ 70 +
        2970114321685595865941457298242052142475650239809883856529911374460811) * 10 ^ 70 +
        9090048303718968506423985640634872932468489463451526038354050040783841) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 109 +
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
  rw [recurrence5Scalar0Left_coeff_285_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_286 :
    recurrence5Scalar0Left.coeff 286 =
      -(((((40180930082638558824893655110298042434288974950789659292346398441325 * 10 ^ 70 +
        3276016360875365411554831658593143456436617043207432257248843620902737) * 10 ^ 70 +
        5747496410312780156531819867800755342745201920901140199381766180971778) * 10 ^ 70 +
        8432351049443697829091580632513840366565949676331070690610061543632704) * 10 ^ 70 +
        2836539918412354963153798005842630209353540122395521969368904483679007) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 110 +
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
  rw [recurrence5Scalar0Left_coeff_286_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_287 :
    recurrence5Scalar0Left.coeff 287 =
      (((((14860251006301894478299829471357721267443872896173680005978521219505 * 10 ^ 70 +
        6302055463378261608604932002275709776481152146807270647726505032393697) * 10 ^ 70 +
        9965997825829432939428614149003865532408221570691014256513856864355682) * 10 ^ 70 +
        7839083915250967973054342869703019976022426798747662398401475731020607) * 10 ^ 70 +
        4531007689231703462063013690986675596765451098027450786699405007872229) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 111 +
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
  rw [recurrence5Scalar0Left_coeff_287_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_288 :
    recurrence5Scalar0Left.coeff 288 =
      -(((((8215046485848266910864321825101427430497922361712501644367810125240 * 10 ^ 70 +
        3997414350347271651388793700743686803704682308013897259895155405810202) * 10 ^ 70 +
        1294089284942141304788875174102461889934867618232392076084855789436247) * 10 ^ 70 +
        6288509404204246811024868167400063443086123462369143055586310593543298) * 10 ^ 70 +
        2356000080362291515236113318182961245470025518721170084730663213502425) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 112 +
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
  rw [recurrence5Scalar0Left_coeff_288_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_289 :
    recurrence5Scalar0Left.coeff 289 =
      (((((6717636352184986250772835701380504753702882237041596141778937321169 * 10 ^ 70 +
        8399658710949507877203966248674748050196577048714007604020881878229946) * 10 ^ 70 +
        0444650313742820118223730501747243071910945505514632178087420944717520) * 10 ^ 70 +
        9573431120926361028518068515872401776036128028666983203802764464364087) * 10 ^ 70 +
        1219416641061909040897310728968522322003636928304076782578834995526676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 113 +
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
  rw [recurrence5Scalar0Left_coeff_289_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_290 :
    recurrence5Scalar0Left.coeff 290 =
      -(((((5921112849299857353101881392760384788825246322803152254439455127959 * 10 ^ 70 +
        1752679122205593913118913688288350150945558600895796469852031176255229) * 10 ^ 70 +
        6598118928472724740968495138920232005118355465868078442045155384427962) * 10 ^ 70 +
        8350213703622298765365759210645385973456130344045429920207779680314942) * 10 ^ 70 +
        6045949415425534326766822670352577572527840145780326578605297475688563) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 114 +
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
  rw [recurrence5Scalar0Left_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_291 :
    recurrence5Scalar0Left.coeff 291 =
      (((((4869757762093114527334366764552989616874206470070043222542923116480 * 10 ^ 70 +
        2217075305716280791701528928034026858918503467162434731854185920468735) * 10 ^ 70 +
        5624321447323528032375987076021792464691180115534207451630622180823110) * 10 ^ 70 +
        8951413920628387118603111061173719536713296441091230059003307486905935) * 10 ^ 70 +
        0886632793238131261409615423080526703328187743578393296035542165112806) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 115 +
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
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (292 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_292 :
    recurrence5Scalar0Left.coeff 292 =
      -(((((3660950417136797782456355238891519697563937267266074188345148995693 * 10 ^ 70 +
        8323380143470537050939068060423344123730951749318567880932473242997704) * 10 ^ 70 +
        6746430114021603166082227213769554988673392199036257534686662749747495) * 10 ^ 70 +
        9238811325588571260128856267015345330474983279932809609584200826188265) * 10 ^ 70 +
        0383518542099395227104887862467447668965522826007183749294079157848247) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 116 +
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
    rw [show 17 = 15 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (293 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_293 :
    recurrence5Scalar0Left.coeff 293 =
      (((((2537532398636297395167548932158380729147816318269619584860336553624 * 10 ^ 70 +
        9592381319152757911006878317737912810887461881473216678591422269241780) * 10 ^ 70 +
        4079393758068618431788581635301182337220056301083122287414671975739896) * 10 ^ 70 +
        5787189026479902178855256351394867993462302205952396588856611425863996) * 10 ^ 70 +
        7245153196665178587215544335909952409417424859848465899263282216320298) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 117 +
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
    rw [show 17 = 14 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (294 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_294 :
    recurrence5Scalar0Left.coeff 294 =
      -(((((1640242036427899904768865484680469328670921625461414945345620603263 * 10 ^ 70 +
        2422894936774499144802770215324167285431935012496201117707726908014474) * 10 ^ 70 +
        1883214594598359053686785790780901173250291882098851117149820558072231) * 10 ^ 70 +
        5446868223827619628879610319262926057929029899514913361619921680013583) * 10 ^ 70 +
        9883200700259043981437003092605119505596393336133394269052173789581531) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 118 +
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
    rw [show 17 = 13 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (295 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_295 :
    recurrence5Scalar0Left.coeff 295 =
      (((((997929744970919459710014451842600553212480830438796766451635850229 * 10 ^ 70 +
        8944723241544046694358563545321018740484838663406824270181124816027303) * 10 ^ 70 +
        9550019770730221962978288013065703036850729287100907775199088457303685) * 10 ^ 70 +
        3731370916432686530897209457511247835497858213730403528722502828914821) * 10 ^ 70 +
        3408651770987541930979872941667751940875811868734807385704658956536119) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 119 +
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
    rw [show 17 = 12 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (296 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_296 :
    recurrence5Scalar0Left.coeff 296 =
      -(((((575376153586576889425316099223039360111900031267371201694827378293 * 10 ^ 70 +
        8240228642629763246526392782938202172068913782054349358735973167411272) * 10 ^ 70 +
        6173882512560822464189549186036547954158424224227732253911686624928861) * 10 ^ 70 +
        9472801634748307422842177320957735646566363315038357391578844190241413) * 10 ^ 70 +
        3431478408539607345481083482691086766943059292413788118205475882776604) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 120 +
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
    rw [show 17 = 11 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (297 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_297 :
    recurrence5Scalar0Left.coeff 297 =
      (((((315934772611205756294934653552582553562757463443827378733837514234 * 10 ^ 70 +
        6411626871848374841449149466441626854641198920386453086662745878277254) * 10 ^ 70 +
        7829495780668196359248529647231698652263661606159625571127822729924133) * 10 ^ 70 +
        0087756815839500655308059642974063747126493957343215644436835753228363) * 10 ^ 70 +
        1281684494078754235787266204185976032963240206919496504214416341291884) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 121 +
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
    rw [show 17 = 10 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (298 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_298 :
    recurrence5Scalar0Left.coeff 298 =
      -(((((165796818916898510212269817664861872994752555097837780074968989454 * 10 ^ 70 +
        0927385126521692511157051957565559044624551153707653614316003404872398) * 10 ^ 70 +
        1433484307643704405032971682488739501650628631935600575118642776814590) * 10 ^ 70 +
        0029200475665748276702538378810615408055140534126916116516421802273191) * 10 ^ 70 +
        1247785781164198300654483630254142840313300215504823643268230951180909) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 122 +
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
    rw [show 17 = 9 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (299 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_299 :
    recurrence5Scalar0Left.coeff 299 =
      (((((83376137178272288699650232526030323497360250752742917366326150219 * 10 ^ 70 +
        8397680736163653647407783643215270906241715185299654782247082465198579) * 10 ^ 70 +
        3256004689716995618333049388104307620225984000302266141836343145006981) * 10 ^ 70 +
        1469027031245630995844887656204577208375458104299609082158408965318022) * 10 ^ 70 +
        6812894075231694097461954276923471225294032992685796567895089552175511) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 123 +
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
    rw [show 17 = 8 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (300 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_300 :
    recurrence5Scalar0Left.coeff 300 =
      -(((((40268757034213267318446599749268741560652901504701992463127403572 * 10 ^ 70 +
        3402480370363223485913213380450016156163144064850250921843188152030049) * 10 ^ 70 +
        5139727937865087993818264493434498536928876215065961696066442425121974) * 10 ^ 70 +
        1136688227856030674216253913007123867119471370222129093520700703555271) * 10 ^ 70 +
        3418424450271009846365529667464030077640450284657610682900273012299495) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 124 +
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
    rw [show 17 = 7 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (301 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_301 :
    recurrence5Scalar0Left.coeff 301 =
      (((((18724216617516428253236266020236239223188391201411930404874933117 * 10 ^ 70 +
        5964973342893463036356964791164377267740687246703050688476900274846919) * 10 ^ 70 +
        8541966328186315318021276818612943114462976548869935878568906683552328) * 10 ^ 70 +
        3202215344930749894488271955440643546201886882010050373754575231802453) * 10 ^ 70 +
        6005904607500346737208140275500661967563317921861611475693425138662990) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 125 +
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
    rw [show 17 = 6 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (302 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_302 :
    recurrence5Scalar0Left.coeff 302 =
      -(((((8410886760660904068279510796437526983183616410136227173809841318 * 10 ^ 70 +
        1343700023189549530358515755989085200541798848641004359277562565536918) * 10 ^ 70 +
        0411940511855848248543572045286565180288398448672214738232935330643756) * 10 ^ 70 +
        7461412438370812318315766465557306997661576263895579265468314042662608) * 10 ^ 70 +
        8117180382503888902329507526366217698955932167862228677884537408469235) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 126 +
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
    rw [show 17 = 5 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (303 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_303 :
    recurrence5Scalar0Left.coeff 303 =
      (((((3671143590960913309875880466878569156179258894110125753758603685 * 10 ^ 70 +
        0423084131011028980491459235810093890781831442757895512915306550688503) * 10 ^ 70 +
        2840626761301935087909642879872667234041809609260025185424107551561289) * 10 ^ 70 +
        2597142144339838031595998570695923199397995060166731956220368906303064) * 10 ^ 70 +
        9193122333767165405253690735311415352737143289659942175724196635588139) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 127 +
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
    rw [show 17 = 4 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (304 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_304 :
    recurrence5Scalar0Left.coeff 304 =
      -(((((1572798341623594103198946790187366702624862624189548775720272086 * 10 ^ 70 +
        9505881463945774453360331286381346270501447893000108633550448193270531) * 10 ^ 70 +
        6646641776560085500458980712009600748421520328149428248151972005907127) * 10 ^ 70 +
        6332228226432136087322798974274557741670073802565875677554129751581216) * 10 ^ 70 +
        7079422672671950059629433799695714435664919875536303409852952867969084) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 128 +
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
    rw [show 17 = 3 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (305 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_305 :
    recurrence5Scalar0Left.coeff 305 =
      (((((672459471048328478921700308853627022793400896660847615746643313 * 10 ^ 70 +
        9597612307144331518444835607075334134450246484200583460701270923941980) * 10 ^ 70 +
        2164504907479373520184161895110802992938350672211663685983326463844103) * 10 ^ 70 +
        9579269627124312315675663355555205058748678150218713185660668799683854) * 10 ^ 70 +
        1016967696097556695280925075207796350379068765254961376580229628596371) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 129 +
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
    rw [show 17 = 2 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (306 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_306 :
    recurrence5Scalar0Left.coeff 306 =
      -(((((293789223423945766408982716220716045942181771665585798543026998 * 10 ^ 70 +
        0136408916069012103718124909978396907724126899673403483235279752811367) * 10 ^ 70 +
        8296336499452417105561751505432620481652009960262987950291297618620405) * 10 ^ 70 +
        6883299107668097140899967336590859385432011583830014707880427004165797) * 10 ^ 70 +
        0296232401616897125603826732525904743899474214504089136257457692175663) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 130 +
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
    rw [show 17 = 1 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (307 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_307 :
    recurrence5Scalar0Left.coeff 307 =
      (((((134577079616470379205841806964552560470673877884719414144152178 * 10 ^ 70 +
        4931330279372412897087546809964997531804621428998358744259518887863146) * 10 ^ 70 +
        6167818270993043560560800650783416226542956317362210951280800930448718) * 10 ^ 70 +
        1643823394379510407640272357600569407809748193721576218340867219509164) * 10 ^ 70 +
        0958467544157221122786148080979252990420332052755040214575477283155149) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 131 +
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
  rw [recurrence5Scalar0Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (308 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_308 :
    recurrence5Scalar0Left.coeff 308 =
      -(((((65695228550390140827279717588632375922457460071097172058860978 * 10 ^ 70 +
        6603795432797210872335369294489136479482076501582614484023555772085080) * 10 ^ 70 +
        1990686743201499362632184642209664557879868628587762389185108857285336) * 10 ^ 70 +
        5161550548943319047363304055352611999851715928902378591630056635270386) * 10 ^ 70 +
        2190376001497461661764015911319633392796859687031434057144126989785268) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 132 +
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
    rw [show 49 = 31 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (309 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_309 :
    recurrence5Scalar0Left.coeff 309 =
      (((((34057369510311176213951855504200712636521482395929029028003179 * 10 ^ 70 +
        8465131667263863564856511692214151745695289387075256021910568011224931) * 10 ^ 70 +
        3224420143679990246655259748463066636897518340006322565715059496641723) * 10 ^ 70 +
        4177113854596779607780242817497045607899501098381939187834183077726943) * 10 ^ 70 +
        0478440625008682294414414592717769541558739851399324771588377158990897) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 133 +
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
    rw [show 49 = 30 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (310 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_310 :
    recurrence5Scalar0Left.coeff 310 =
      -(((((18366096495656180361663393535530947176993687258948212598338470 * 10 ^ 70 +
        9278934232402859898149087274093176049981802878730768806949730269223354) * 10 ^ 70 +
        0791105175846733732782078137493827313706279082868551044335328303237541) * 10 ^ 70 +
        2171264780678884877814126730600645363932290254497330650759186913571196) * 10 ^ 70 +
        0878628582001800258638073388561006241756640359109936000830090615835526) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 134 +
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
    rw [show 49 = 29 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (311 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_311 :
    recurrence5Scalar0Left.coeff 311 =
      (((((10042270539578829328674788880456400636162720981013141905479731 * 10 ^ 70 +
        5994368270217661521614199379617762839870388330073406459813097290327053) * 10 ^ 70 +
        9511905581739181345914482097146620958872137481981872905066826009029994) * 10 ^ 70 +
        0864985045104535699543037536641001829691664664893124300053323170963442) * 10 ^ 70 +
        9928904112919422137781358271570875071573923305190029152181226888275172) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 135 +
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
    rw [show 49 = 28 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (312 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_312 :
    recurrence5Scalar0Left.coeff 312 =
      -(((((5452798881221061159256913954499108078817763485277800428332793 * 10 ^ 70 +
        1130259417537121629066397359083255062984780316489890997632225983310439) * 10 ^ 70 +
        8007191939785312138318409702694111438514711769613184329541035402446312) * 10 ^ 70 +
        2167057876813215051383143339245877190302636792299428226101583563216001) * 10 ^ 70 +
        3232710875822936818610836937067872589387014267800405417452374727930368) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 136 +
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
    rw [show 49 = 27 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (313 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_313 :
    recurrence5Scalar0Left.coeff 313 =
      (((((2901110380642133921172074926667308103446808433256222397483275 * 10 ^ 70 +
        7007781007949147582088712092177441873252246103726631852253562969976439) * 10 ^ 70 +
        7923853368554501206142467609598586261849284929607536715191388764886048) * 10 ^ 70 +
        3077850230021231976585520716699743217213568208944080277222157787997105) * 10 ^ 70 +
        5110672456617830256750856777482426993471093548248912950896610213436386) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 137 +
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
    rw [show 49 = 26 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (314 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_314 :
    recurrence5Scalar0Left.coeff 314 =
      -(((((1501339106208967045813265633044432220404088270783025024889395 * 10 ^ 70 +
        9048596688662889881250173043421831509461944914183734252458520100363689) * 10 ^ 70 +
        3564393885326248589988887798816135133074431450781765514841790529669998) * 10 ^ 70 +
        1047779414580563572927748014869145675970408216689944380448575777988353) * 10 ^ 70 +
        1953472128578945304839315697258750541340440048219761702578635607658983) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 138 +
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
    rw [show 49 = 25 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (315 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_315 :
    recurrence5Scalar0Left.coeff 315 =
      (((((753162437551918733032035120857509112931343435411936175080995 * 10 ^ 70 +
        7061104731468507146243964276314167680136243344353709870517723813514135) * 10 ^ 70 +
        2582266294735334738813324180173202431321332346959168784505534362322461) * 10 ^ 70 +
        2739388278611326088527943014532989662578684717747721206074710260187024) * 10 ^ 70 +
        8977345540626001081853696072919541494425728160971272880178239132439502) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 139 +
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
    rw [show 49 = 24 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (316 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_316 :
    recurrence5Scalar0Left.coeff 316 =
      -(((((365882682161826176130870757780208920198879392970154999065326 * 10 ^ 70 +
        4653348662399730885221370115731795155154795252466204672631150934589547) * 10 ^ 70 +
        4251901631383299555684226349486617874306619840677823696366692166925749) * 10 ^ 70 +
        5317993370146697195144227158139896106769267318590979944598235922945799) * 10 ^ 70 +
        8207172380860477146452438027940652745306699408482456306938305723431970) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 140 +
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
    rw [show 49 = 23 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (317 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_317 :
    recurrence5Scalar0Left.coeff 317 =
      (((((172188645288150684092713914189092213302817576653535914390097 * 10 ^ 70 +
        2912676664917598886590322142629583594598138530211521509952319999620176) * 10 ^ 70 +
        4639670260800498235388821203161758465201300056008975483101607263302764) * 10 ^ 70 +
        9030541096309955346493154087844324424851028896091640407059981718452947) * 10 ^ 70 +
        3083966497379281282421643069302575561036302845909441958335111245099681) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 141 +
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
    rw [show 49 = 22 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (318 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_318 :
    recurrence5Scalar0Left.coeff 318 =
      -(((((78609398021883278494842019243187341376222538627123461634610 * 10 ^ 70 +
        1245648980496091639330475477158922142137559724538156179138248437244073) * 10 ^ 70 +
        1750972396355671207100066033441237481664301988405096857239586171827957) * 10 ^ 70 +
        1040677195965556697667513743364485872392610807957323587916358825664761) * 10 ^ 70 +
        6724119566035045637018734158724577156703840491112092434378293871335700) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 142 +
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
    rw [show 49 = 21 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (319 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_319 :
    recurrence5Scalar0Left.coeff 319 =
      (((((34893680293938895296427574243208802458364832753197888303072 * 10 ^ 70 +
        1449035966389106087399779839305784209804424934681974747925284657359171) * 10 ^ 70 +
        1303405873310211099721186827243394757995928988843291946757097304428689) * 10 ^ 70 +
        5916924777269193906631716125489025045844829024325576896498031280302098) * 10 ^ 70 +
        6600051355996812082662576626242418192420706344444929406873518743782506) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 143 +
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
    rw [show 49 = 20 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (320 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_320 :
    recurrence5Scalar0Left.coeff 320 =
      -(((((15110848263714219305750960935959822350881373204801215079897 * 10 ^ 70 +
        7090341472062985329678193387010573644781639273657710579219726353708907) * 10 ^ 70 +
        1699142105610401764855661639419539108688992526652016629363471576350186) * 10 ^ 70 +
        7725509542785432499773069833930899550747239224612204746552727522031449) * 10 ^ 70 +
        5612127785806253121636657398067388218225373666369700240113887343125542) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 144 +
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
    rw [show 49 = 19 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (321 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_321 :
    recurrence5Scalar0Left.coeff 321 =
      (((((6414969816237585136236875430020513893984480426951665833974 * 10 ^ 70 +
        3683527400222968248763189230890555251434100839225249021960623875846147) * 10 ^ 70 +
        0911256360282167475675045006524948146876810710615034274927144605784223) * 10 ^ 70 +
        0940853286254439797023759537095104686820968042898086540956336514728389) * 10 ^ 70 +
        0630851858778316738960945574800315693712229573520111029047004945499624) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 145 +
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
    rw [show 49 = 18 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (322 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_322 :
    recurrence5Scalar0Left.coeff 322 =
      -(((((2687631572727858780907933911324609107063279741599704811960 * 10 ^ 70 +
        0210829144293370375522987355764433902853236228336463995923593667381946) * 10 ^ 70 +
        5175963704676198273799191858866098185806205615640312733561954850349359) * 10 ^ 70 +
        0678720037386992170724834281674049152798534839997030699534435550407430) * 10 ^ 70 +
        9468366672984841986585790555718386042472182198278128761093921571015792) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 146 +
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
    rw [show 49 = 17 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (323 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_323 :
    recurrence5Scalar0Left.coeff 323 =
      (((((1121095443700394660445838530504904913237418068139704078278 * 10 ^ 70 +
        9910184730097808558931522098997419223513432285874126659082883828575930) * 10 ^ 70 +
        1239315171132872382781967880399148410632224276993027503574018019256154) * 10 ^ 70 +
        8757628505660437190931438809467965288207629606115784962034409886520709) * 10 ^ 70 +
        5965724529752939586217511641928312220771480417915092361818442319424682) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 147 +
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
    rw [show 49 = 16 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (324 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_324 :
    recurrence5Scalar0Left.coeff 324 =
      -(((((470554331284581195464846744122346923840556077106089900634 * 10 ^ 70 +
        4113988279670499920573990938262458923514083045259607469563847144090592) * 10 ^ 70 +
        5352275358834734442434829879034102483162688320502240886562233917407052) * 10 ^ 70 +
        3729974170431126860963018212996177222269255837715988875751440051141608) * 10 ^ 70 +
        8581731002233440685910182730917455726878012661790001435711973493511388) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 148 +
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
    rw [show 49 = 15 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (325 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_325 :
    recurrence5Scalar0Left.coeff 325 =
      (((((200906573797128150799410248316976266993667748914125155995 * 10 ^ 70 +
        9289779414400737599383854436935184065017972168562754132433433212901152) * 10 ^ 70 +
        3430054305384327123877458717739528616724342849361780690873416934123350) * 10 ^ 70 +
        6732287459182069076160126409680069681836851714024762460355392797934380) * 10 ^ 70 +
        1550657891306656228835704772427976036156899934050052833335465807674973) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 149 +
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
    rw [show 49 = 14 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (326 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_326 :
    recurrence5Scalar0Left.coeff 326 =
      -(((((88001946713976769573678920369687817367064129703553056428 * 10 ^ 70 +
        1524728019635675496003101414020948985372060214710610510935966060195549) * 10 ^ 70 +
        9083175214943168277672322477136982210771030563078604595683533807086915) * 10 ^ 70 +
        9229083453158197258083679068291094762534507820096909871890000849594196) * 10 ^ 70 +
        3553603387437330118686374920959902486464542773040857848897732094669700) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 150 +
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
    rw [show 49 = 13 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (327 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_327 :
    recurrence5Scalar0Left.coeff 327 =
      (((((39679076713899295660939153937979380766537386851034523773 * 10 ^ 70 +
        0735996204632218242356280147527530761023188524716402560631411672089630) * 10 ^ 70 +
        0387080900143704393092427454012374299648630256834339709696379246069902) * 10 ^ 70 +
        3286952787445175176263295979169192181671567360810626514761851897635429) * 10 ^ 70 +
        2402821013600653157788843424894172324598948494619295379353651082206793) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 151 +
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
    rw [show 49 = 12 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (328 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_328 :
    recurrence5Scalar0Left.coeff 328 =
      -(((((18362012124147845426059635478257687770847830186477067360 * 10 ^ 70 +
        7363360145978741334067140626938818977008503433963527563426264199048530) * 10 ^ 70 +
        8466364176457480793091025392505133284770877055099272000350207761568603) * 10 ^ 70 +
        4268797931239814732772155604082331417774909291393604749828493349296675) * 10 ^ 70 +
        3643969545803823003496033318611990994926476795225928165262370865826596) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 152 +
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
    rw [show 49 = 11 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (329 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_329 :
    recurrence5Scalar0Left.coeff 329 =
      (((((8652476086588773003731182123923636774346483832403703229 * 10 ^ 70 +
        5251022961846433106158649443962737492746459801116346572744525658464161) * 10 ^ 70 +
        2539420844885028299318043204038042867208023888342359629144546866270613) * 10 ^ 70 +
        6530343936099762610092195753433612980374150311763480400602400861699563) * 10 ^ 70 +
        6496461398081881531982332418347627671789884646727962008853096764016592) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 153 +
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
    rw [show 49 = 10 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (330 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_330 :
    recurrence5Scalar0Left.coeff 330 =
      -(((((4110452857555212153407741051208641014994583272341626358 * 10 ^ 70 +
        0606776806454625532992493478581594152852198682928734824668804779526393) * 10 ^ 70 +
        4246462375087927903581328834614802838616872088952498209709012762594916) * 10 ^ 70 +
        5802337438679156875131194024996875374984195279536010642772561852441224) * 10 ^ 70 +
        2586243499102382297462294351591085922203886427627481767953922350394187) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 154 +
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
    rw [show 49 = 9 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (331 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_331 :
    recurrence5Scalar0Left.coeff 331 =
      (((((1950083349234973605235406178935135163725830049740434758 * 10 ^ 70 +
        4529475961993783113032950772823184975242334524468936439173799233387633) * 10 ^ 70 +
        1384327263038667435680819438809829464429064307311110100932829344569393) * 10 ^ 70 +
        4578140733798539447717912063586745374060732761164442059143687780232444) * 10 ^ 70 +
        7799167481855943572210442731872737300900726073791649412465669208651171) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 155 +
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
    rw [show 49 = 8 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (332 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_332 :
    recurrence5Scalar0Left.coeff 332 =
      -(((((916914037481422170235090235861683659323034383349959509 * 10 ^ 70 +
        9397186417506572625840915637490121114333234754339879906193331746529218) * 10 ^ 70 +
        2069731016416616833453269831325691075648773472676686482519679515141982) * 10 ^ 70 +
        7099632518191674720548377598829331165208624663127116995881695263318392) * 10 ^ 70 +
        1979835801152609856500859916076760906171015268387553269597170888105216) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 156 +
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
    rw [show 49 = 7 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (333 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_333 :
    recurrence5Scalar0Left.coeff 333 =
      (((((424958548136031180749402751661568260059158677989925738 * 10 ^ 70 +
        0683693225139648274375213121256517545669379881711457940182343950643517) * 10 ^ 70 +
        9230651061021016326065520453326720485524008743969361409025052762231690) * 10 ^ 70 +
        4506550192910770380860324799953536124641246028922116403606100933166166) * 10 ^ 70 +
        5719873247705944289704915346044506752127876686512653262816817364884882) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 157 +
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
    rw [show 49 = 6 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (334 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_334 :
    recurrence5Scalar0Left.coeff 334 =
      -(((((193436491809578144428751943630534060921806616484245911 * 10 ^ 70 +
        7104072397538608038499888555265128377264333076110590016139468525614492) * 10 ^ 70 +
        9837038044682317656453938186374911354781562090777579513396050420554652) * 10 ^ 70 +
        9523862055255476646987067980721005073164477273389030808998261446262291) * 10 ^ 70 +
        9000249623734147565282237679801494047108388080785367024813810702421581) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 158 +
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
    rw [show 49 = 5 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (335 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_335 :
    recurrence5Scalar0Left.coeff 335 =
      (((((86284149112451693187851671993243165138322797770314301 * 10 ^ 70 +
        4242298712291618592569553398566946069825419111920830911740234448523956) * 10 ^ 70 +
        6546768377352257160621846140541022835619859781602241269475674926857920) * 10 ^ 70 +
        2098343688030320978547831932798342365486599095754653036659123051336674) * 10 ^ 70 +
        8396222653702279387143424078227168344686687878086766473573649276373112) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 159 +
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
    rw [show 49 = 4 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (336 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_336 :
    recurrence5Scalar0Left.coeff 336 =
      -(((((37666644419826888921557858151316755980047080130224023 * 10 ^ 70 +
        1967193646388141531157021922545834365685403081262171846137785497804237) * 10 ^ 70 +
        7819932709066084214583136759790484023679200174605685536941374929031270) * 10 ^ 70 +
        3946198793867021392377229200134515544676732561819146603345138414523194) * 10 ^ 70 +
        8841351816557892076165257518004328826986091641051324782250425943805985) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 160 +
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
    rw [show 49 = 3 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (337 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_337 :
    recurrence5Scalar0Left.coeff 337 =
      (((((16080784886895706933952695845435546593529134683594136 * 10 ^ 70 +
        2056442287900716861531572490960021419855282211877730014739352219647219) * 10 ^ 70 +
        1022702523004434097053403514270586437151067444017177009715095414585707) * 10 ^ 70 +
        7888648155156223312435791500852906843243967126354953341537813120657628) * 10 ^ 70 +
        4769793225132958710867009040398689586848409990490845577487572893935378) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 161 +
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
    rw [show 49 = 2 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (338 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_338 :
    recurrence5Scalar0Left.coeff 338 =
      -(((((6711609028359905113959351836372222786082164532371756 * 10 ^ 70 +
        7855100678506628725395666829438049534436791370724572539804057918683425) * 10 ^ 70 +
        9615943807341192785107634520900717462430772568950188507240652700889505) * 10 ^ 70 +
        6724103497553292579457186765723651250419529412503212337950499460565249) * 10 ^ 70 +
        3725975391935935752600604557560220202005390075552345817541979305923960) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 162 +
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
    rw [show 49 = 1 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (339 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_339 :
    recurrence5Scalar0Left.coeff 339 =
      (((((2738048859253106189787070831689736525648085398516192 * 10 ^ 70 +
        7917535458788734302730985015325853848643869739487031078878534890458323) * 10 ^ 70 +
        0295064626344512052720572563979483425796035926399562558249148807489036) * 10 ^ 70 +
        0967015371970058874186034952029838842590855214252107949238020848284542) * 10 ^ 70 +
        4402003215609962482656393839841498594551707636754785063470537683649028) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 163 +
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
  rw [recurrence5Scalar0Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (340 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_340 :
    recurrence5Scalar0Left.coeff 340 =
      -(((((1091714116899343337922542061468702018456906339166359 * 10 ^ 70 +
        8417918966440797463739370263355479901189656028754398554925996886349803) * 10 ^ 70 +
        2988234803333149036863604432665166758071604390631954757816665011730699) * 10 ^ 70 +
        7296247684201606241399847362263288578793378332310752020933759620424108) * 10 ^ 70 +
        4358712214397997006621425250715825701716832202013954252069019213353966) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 164 +
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
    rw [show 81 = 31 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (341 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_341 :
    recurrence5Scalar0Left.coeff 341 =
      (((((425388435897654470777195228682946191040598513172545 * 10 ^ 70 +
        9178665163715469904772142083636993156268262198998456388024060727774309) * 10 ^ 70 +
        1984343052924658097841020814315795747325761244455453212901920761499185) * 10 ^ 70 +
        1677450555210569980689697105234340432764974304501912950837827374762178) * 10 ^ 70 +
        8597998117723361557089880694506250535873126912558475215086713917337136) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 165 +
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
    rw [show 81 = 30 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (342 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_342 :
    recurrence5Scalar0Left.coeff 342 =
      -(((((161957168141125779423597157919452534100611533928081 * 10 ^ 70 +
        2959217890660905925471949871060176790747293129939293604305188052772009) * 10 ^ 70 +
        0198720125939553337358109265375150016418198530901941906667982576003243) * 10 ^ 70 +
        6568830017135470735083858243763312554724264570214774599058775564990177) * 10 ^ 70 +
        7407788651797552755651690396653240394951039665163123835460452586408445) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 166 +
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
    rw [show 81 = 29 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (343 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_343 :
    recurrence5Scalar0Left.coeff 343 =
      (((((60232951965623436850002172050525418814435943108994 * 10 ^ 70 +
        0372604453980484999970908312955765050113743018520782372466327609087951) * 10 ^ 70 +
        3102935736018626298876138381508319497249648492934787216221759102434697) * 10 ^ 70 +
        5517223614298052665093666365248370748999439552390309922351886289720854) * 10 ^ 70 +
        5704347780381980829550404696129967975843481886166208555843304936464306) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 167 +
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
    rw [show 81 = 28 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (344 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_344 :
    recurrence5Scalar0Left.coeff 344 =
      -(((((21872773653825969353990552842041869818102505878691 * 10 ^ 70 +
        3540894706725533093851870786116623711967007957105065541778036473946281) * 10 ^ 70 +
        7581530554624905229415724493813093843626361108912827519315367970768353) * 10 ^ 70 +
        7163327215056190151990947780088106324905498391552176424656486898975285) * 10 ^ 70 +
        9334025512371420618380687607046594708833539939198386170438212582146006) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 168 +
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
    rw [show 81 = 27 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (345 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_345 :
    recurrence5Scalar0Left.coeff 345 =
      (((((7750669259986380030399133670226590817240360808811 * 10 ^ 70 +
        7836387444253291913347767569994983480435571012068171463184826877874816) * 10 ^ 70 +
        0985652629565057473762516932044390215986589942219455214511575975617756) * 10 ^ 70 +
        7315810156405011146285227991724736537179609023061566899279830416772719) * 10 ^ 70 +
        5046595779295865215751759022075544120510486422808311025493211910365864) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 169 +
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
    rw [show 81 = 26 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (346 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_346 :
    recurrence5Scalar0Left.coeff 346 =
      -(((((2677661336138677747910914193684987059123916670593 * 10 ^ 70 +
        5400312074654906558987448481296176537160717834005236743205562517587750) * 10 ^ 70 +
        5596580572310220930127114814764330144184933551928551264059094444330426) * 10 ^ 70 +
        9990840983427022520378010553954605138971805111370690105364752273201465) * 10 ^ 70 +
        0205507215371095054204414470528914838295518095333493478145473428742782) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 170 +
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
    rw [show 81 = 25 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (347 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_347 :
    recurrence5Scalar0Left.coeff 347 =
      (((((900765368112635491366457107184521028219155303891 * 10 ^ 70 +
        2543913862326727516821287191766921354429989118997626835433660112144772) * 10 ^ 70 +
        1367055125464674699188856818417712837731904247518950312406153721416080) * 10 ^ 70 +
        3564026460395408431431799477755204821993174198998714391788104437025940) * 10 ^ 70 +
        5931020976962079524025707542188352178809008630189034905185942438298148) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 171 +
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
    rw [show 81 = 24 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (348 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_348 :
    recurrence5Scalar0Left.coeff 348 =
      -(((((294536793670391276724313303490745395003012916531 * 10 ^ 70 +
        9141797216115657796352819870702794638193940257458109938848709436298211) * 10 ^ 70 +
        4745550967921920350299995228354179576582990594393867902457330957818184) * 10 ^ 70 +
        9705302075829753466970062844124396150526690660034004290384570547032715) * 10 ^ 70 +
        6523044166347992966515555172024820145412921145238570907003742861035409) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 172 +
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
    rw [show 81 = 23 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (349 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_349 :
    recurrence5Scalar0Left.coeff 349 =
      (((((93374105433637686768136637805834887273365547826 * 10 ^ 70 +
        9087224172351656344663100083132225234121674461830609935706841651675705) * 10 ^ 70 +
        3684688432273389471325437347238841263039227693504867356004590815778738) * 10 ^ 70 +
        3135385979826887906272415454029226063336510659541694945425688199873150) * 10 ^ 70 +
        7950541156648675983720940958155781762425381459363743992326445574761158) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 173 +
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
    rw [show 81 = 22 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (350 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_350 :
    recurrence5Scalar0Left.coeff 350 =
      -(((((28589062639742545506205525889545404851430383012 * 10 ^ 70 +
        9262534225354482539618279405643349981598305026377651455542340565982680) * 10 ^ 70 +
        1626317352691810424579933199718959470467111548076526433814142563528690) * 10 ^ 70 +
        7695610208058970950586698684917690220314055679326567099742688689088198) * 10 ^ 70 +
        6927177152075575783722993103872885164892884427512286928036583085071934) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 174 +
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
    rw [show 81 = 21 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (351 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_351 :
    recurrence5Scalar0Left.coeff 351 =
      (((((8402615965256606666553700842238360044312829138 * 10 ^ 70 +
        4532503827041421817097395950190298438990266824523133530824905756066075) * 10 ^ 70 +
        4944382036586391953241442734802047920244288088332165619877170615279036) * 10 ^ 70 +
        0620473221740441804908863440761958696797200395697758855639609858286809) * 10 ^ 70 +
        7339871453291351294850115649249971937901777209932462886316566543158716) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 175 +
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
    rw [show 81 = 20 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (352 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_352 :
    recurrence5Scalar0Left.coeff 352 =
      -(((((2346289498475325663262113612002199720964923689 * 10 ^ 70 +
        1955872878160488908648128400094913577163970643263920434142857676028361) * 10 ^ 70 +
        1048746397207146059211346004483752174843628829501292770824107788793112) * 10 ^ 70 +
        4133028436010222818857135609322971147256185344058054481479939552605664) * 10 ^ 70 +
        1255279508736509441247251543684015884362158184802137307832199443436060) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 176 +
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
    rw [show 81 = 19 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (353 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_353 :
    recurrence5Scalar0Left.coeff 353 =
      (((((610498595252305402878012962944759774107801034 * 10 ^ 70 +
        6982509467962306516060113401663447235348523392114917685498831575945948) * 10 ^ 70 +
        1283383702244332695336571324731637729117047878127432890178096232930825) * 10 ^ 70 +
        6807822066233168677909498601690927935747812735004234494765594921539394) * 10 ^ 70 +
        7492647767888701978756627257435445984136551434564167989455633748076412) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 177 +
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
    rw [show 81 = 18 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (354 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_354 :
    recurrence5Scalar0Left.coeff 354 =
      -(((((141866901424745152563001830062219744070245291 * 10 ^ 70 +
        1045596958607796207945658099822778062409336854199539794543751208929155) * 10 ^ 70 +
        7556061583334508046556402425454631012724867918062867920338868483976049) * 10 ^ 70 +
        4701784508695676315752985132593175661479148452786925500221001627975512) * 10 ^ 70 +
        0090978244843441706221631475362407319001353611717619122680829744052145) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 178 +
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
    rw [show 81 = 17 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (355 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_355 :
    recurrence5Scalar0Left.coeff 355 =
      (((((26002417964176006053077378497663148472905506 * 10 ^ 70 +
        7111231570626789555998744853903574224214679551949908465401110766093619) * 10 ^ 70 +
        1293389833004107865324037256569949339878855581143970217394517218822979) * 10 ^ 70 +
        2746682030350558982299352755213191092186664364169785250417732471775782) * 10 ^ 70 +
        3374754186759274382636639353558302541320368235268846010313905769152100) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 179 +
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
    rw [show 81 = 16 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
