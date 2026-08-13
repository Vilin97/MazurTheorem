/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart1Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
