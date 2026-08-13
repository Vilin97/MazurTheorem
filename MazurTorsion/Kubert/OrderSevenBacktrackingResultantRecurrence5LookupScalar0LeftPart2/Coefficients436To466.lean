/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart2Simp
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

private theorem recurrence5Scalar0Left_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (436 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_436 :
    recurrence5Scalar0Left.coeff 436 =
      -((((8075161663373116118366268987761956306624582183704146 * 10 ^ 70 +
        4502750422634095776023223102994066949788517648650674389117180845192443) * 10 ^ 70 +
        4771997740458904080739408502299419211754086736351373691485924451352273) * 10 ^ 70 +
        1963836691214681757442514620108312469089839644239488675171579423331006) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 260 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 31 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (437 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_437 :
    recurrence5Scalar0Left.coeff 437 =
      ((((82780421000655176887155675459447343895187070250495 * 10 ^ 70 +
        9900759235044944836787532873538731219266903479047933383555628760595683) * 10 ^ 70 +
        3144446730983327002848262349042317616092422970022554151713587745676030) * 10 ^ 70 +
        7993351153458223038124198541672080713726053095654536061082841240856762) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 261 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 30 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (438 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_438 :
    recurrence5Scalar0Left.coeff 438 =
      ((((1944574044519272530654683868500377464544643799042 * 10 ^ 70 +
        5735904543033178867241221497541225867866869414552648294323372924765952) * 10 ^ 70 +
        1755990130566258277700304392510047751616023518024714068311666884413439) * 10 ^ 70 +
        3509497818672154931670546816761857201232287141361250796858743944858804) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 262 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 29 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (439 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_439 :
    recurrence5Scalar0Left.coeff 439 =
      ((((11999545066190546085634151919671638596609726851 * 10 ^ 70 +
        3013121274012369441542871969962543813880451410854862856800336368272659) * 10 ^ 70 +
        4317246671482079473110101080246306034546158924106508665350346844787629) * 10 ^ 70 +
        0628686309315845336916596732130495733380896153789053572783693369002859) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 263 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 28 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (440 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_440 :
    recurrence5Scalar0Left.coeff 440 =
      ((((2767077557464517914136770145875785967051518 * 10 ^ 70 +
        2222280430662811073761291552639820367946913401505024875628629022164087) * 10 ^ 70 +
        4866489013343982443808548861052024430467747586192596091474067850911092) * 10 ^ 70 +
        2402043754781462180123436090169712077282400720302279825924665760312686) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 264 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 27 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (441 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_441 :
    recurrence5Scalar0Left.coeff 441 =
      -((((300399291120960983384473224335367448481273 * 10 ^ 70 +
        1462099380382058469465634574384250630349239887264206408341935915759105) * 10 ^ 70 +
        3051005570667891121703652935918643407758422724059112294306141330583865) * 10 ^ 70 +
        4684575312841553010983227882990212127296522096662918213441714244938673) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 265 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 26 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (442 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_442 :
    recurrence5Scalar0Left.coeff 442 =
      -((((1213744338637732068459569341284231163111 * 10 ^ 70 +
        9465635111948536643292898765842592493337680767753818681918899024618104) * 10 ^ 70 +
        1948518431982025989703016908669780637909119601993239500884445987283056) * 10 ^ 70 +
        5670121808380396308373472585420920118736879385350859495746459242470650) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 266 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 25 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (443 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_443 :
    recurrence5Scalar0Left.coeff 443 =
      ((((288449108565617703429558818394576303 * 10 ^ 70 +
        1813695424467024650701359252074344730882224377288862319246956573970114) * 10 ^ 70 +
        6347134711298305085978128786047916421762070685464459828551603866451567) * 10 ^ 70 +
        5776806226323673665732502011339876580914558545939035160775968967708249) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 267 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 24 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (444 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_444 :
    recurrence5Scalar0Left.coeff 444 =
      ((((12148217784796596403423188925556082 * 10 ^ 70 +
        3973848871967208610325367628436596899201605230384134622904015989561850) * 10 ^ 70 +
        4992254131756659096501473480950202369837214133146339848664172125814298) * 10 ^ 70 +
        1666637888919131453695430058121330277505307676118998873370284668501724) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 268 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 23 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (445 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_445 :
    recurrence5Scalar0Left.coeff 445 =
      ((((18505635263666432597306118816961 * 10 ^ 70 +
        5123534551791829068080469547119745663800607426434218945153706855624813) * 10 ^ 70 +
        2386758346031408183125862491061694202530904217714081793896090871754862) * 10 ^ 70 +
        2376605170497932036734437747113475055702397227575414787170009991461980) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 269 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 22 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (446 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_446 :
    recurrence5Scalar0Left.coeff 446 =
      -((((42160540692536603002776439626 * 10 ^ 70 +
        5934333568290705834873002859910817071035846748998843633709982922438919) * 10 ^ 70 +
        5880806658928150458280897473481838013468922511804173683790536785657094) * 10 ^ 70 +
        6882085348149025785223936371440750798487659522608191439150141473363891) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 270 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 21 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (447 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_447 :
    recurrence5Scalar0Left.coeff 447 =
      -((((116597115624936635205233393 * 10 ^ 70 +
        6131927107806538385798183692039629021934147427857067670331282517777052) * 10 ^ 70 +
        9420134260950100620992638036495578526655629206067413454549994734692572) * 10 ^ 70 +
        9248827572925186834768340998957268414155662491288771598291535740210093) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 271 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 20 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (448 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_448 :
    recurrence5Scalar0Left.coeff 448 =
      ((((43091948737969571893123 * 10 ^ 70 +
        9702445485595211027239554444215921408363450845128661542152563328027228) * 10 ^ 70 +
        2138862519757973040676293726230870211162029476464605987657584848220807) * 10 ^ 70 +
        6728532038192943991918112338927901361396143829404233465294303720425246) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 272 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 19 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (449 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_449 :
    recurrence5Scalar0Left.coeff 449 =
      ((((274384931921073543682 * 10 ^ 70 +
        7863010335127897976980785779239885630933584792904732336164632783488854) * 10 ^ 70 +
        3230783697184343950324834101753982288797665389982048589929581434505234) * 10 ^ 70 +
        4110929433200216614618378538458440994607296543683271392847160958135034) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 273 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 18 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (450 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_450 :
    recurrence5Scalar0Left.coeff 450 =
      ((((44354640914010250 * 10 ^ 70 +
        0568038355278870038223744471201792045569829845900791380242961021228046) * 10 ^ 70 +
        4544432441414024943380785820728571339241471236995904632859988770829784) * 10 ^ 70 +
        6036230976824675049624485332757373075675198646268189392847647314567882) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 274 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 17 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (451 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_451 :
    recurrence5Scalar0Left.coeff 451 =
      -((((237591933109763 * 10 ^ 70 +
        3023898545961619114153054790301973394426074446406035369452453287158632) * 10 ^ 70 +
        3211736747602857513523533789013889752710278295036333468118984676225740) * 10 ^ 70 +
        2231743005766631925945975230092459437013827478766411797735623603540574) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 275 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 16 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (452 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_452 :
    recurrence5Scalar0Left.coeff 452 =
      -((((94592018634 * 10 ^ 70 +
        8257470819939773061944860643758624069110243287449855540420367031397392) * 10 ^ 70 +
        8949653151129406058340926046976363692985056515834538127253069237554780) * 10 ^ 70 +
        3345510615732667994545212303943819575219401044620052297228212561153645) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 276 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 15 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (453 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_453 :
    recurrence5Scalar0Left.coeff 453 =
      ((((37448756 * 10 ^ 70 +
        4987202504116287400632227158261523498200398634039559475653251026136965) * 10 ^ 70 +
        5518294901014364788400251223305357108767430623119207209556992139475283) * 10 ^ 70 +
        1180947011921296418429956054388016056982364843835171101191620038338117) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 277 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 14 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (454 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_454 :
    recurrence5Scalar0Left.coeff 454 =
      ((((13067 * 10 ^ 70 +
        4280668196094433268095913956977505654955905429775983108756669767494351) * 10 ^ 70 +
        8303460079948655547647710770648040163694458183936899363137189376736768) * 10 ^ 70 +
        5664180047894286457648281995423697416515259578530696731433273995759399) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 278 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 13 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (455 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_455 :
    recurrence5Scalar0Left.coeff 455 =
      (((1113855004750695573124684856081887631186722955722283482364671206879028 * 10 ^ 70 +
        3180571058366994573482700208673726835174804229618261200165315242885044) * 10 ^ 70 +
        7357978153453080898033323798814461177663116947510584343663392115199544) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 279 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 12 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (456 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_456 :
    recurrence5Scalar0Left.coeff 456 =
      -(((1558164462886008696743538604095447953112931868201812088401036987211 * 10 ^ 70 +
        3876589004394838150366174996471473835248308063803085432268802464722904) * 10 ^ 70 +
        7621365134091091518713086568166044690347298475803537873876187494119522) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 280 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 11 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (457 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_457 :
    recurrence5Scalar0Left.coeff 457 =
      -(((41368527051264106756364297759419835376151015611214854984520213 * 10 ^ 70 +
        2486039875350465275054681254106858804149153039357005681428474213613868) * 10 ^ 70 +
        3683644618625827197611539731765194828933528062745635757304222092803699) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 281 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 10 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (458 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_458 :
    recurrence5Scalar0Left.coeff 458 =
      (((690041809622841400806377331201227588105160431867994847449 * 10 ^ 70 +
        9850695434426847765431771262884452585971316142803507827648252910962856) * 10 ^ 70 +
        5598863206699506215607091752164719681375261287247938471481855131230075) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 282 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 9 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (459 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_459 :
    recurrence5Scalar0Left.coeff 459 =
      (((20049948067989311311192247867458514879405491831289570 * 10 ^ 70 +
        4549027613696155060309673121556653695148212528270630037965724403407584) * 10 ^ 70 +
        8427531724082730370667319281466625802828097477760260542409715708234370) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 283 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 8 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (460 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_460 :
    recurrence5Scalar0Left.coeff 460 =
      (((7011068486435806470751713322106681221590561118 * 10 ^ 70 +
        4353249174687022596847774865867937876833811469115860911976251707659420) * 10 ^ 70 +
        4559223612524319939044828026114925275217449825544997481640459792724457) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 284 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 7 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (461 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_461 :
    recurrence5Scalar0Left.coeff 461 =
      -(((171485060899567974588956373315887701012207 * 10 ^ 70 +
        7419970023730266054094160647373768228777253310263140385348457969924422) * 10 ^ 70 +
        7038335899589789546000267247442850374184296384271120072752614010939046) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 285 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 6 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (462 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_462 :
    recurrence5Scalar0Left.coeff 462 =
      -(((210070199512294400318630368290780388 * 10 ^ 70 +
        7915044350412465181116999709474630756652024319447050835592268083204769) * 10 ^ 70 +
        7325242388376066439627758503488235282656872522518935447523573316386379) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 286 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 5 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (463 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (463 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_463 :
    recurrence5Scalar0Left.coeff 463 =
      (((29584369002337353745116757801 * 10 ^ 70 +
        5207339112204848653220704769176076247311477667088391667713967883190746) * 10 ^ 70 +
        8902022714556596706267844471276204570307913553622171016339583075259176) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 464 = 287 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 4 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (464 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (464 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_464 :
    recurrence5Scalar0Left.coeff 464 =
      (((6951381669698067529678 * 10 ^ 70 +
        7893789903122840672071384548696133963246783127418998105883216194207580) * 10 ^ 70 +
        7151059188419980047495108146958672007546543698856344989189319363687212) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 465 = 288 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 3 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (465 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (465 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_465 :
    recurrence5Scalar0Left.coeff 465 =
      (((246972803287879 * 10 ^ 70 +
        7098219552830294565355737242340753775063149403136849725805225940917873) * 10 ^ 70 +
        3236381951396216500502887336568318675764664131182868377122379781104774) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 466 = 289 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 2 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (466 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (466 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_466 :
    recurrence5Scalar0Left.coeff 466 =
      -(((1899343 * 10 ^ 70 +
        3728578708345950337482853555962780161618422023783390029888900309536140) * 10 ^ 70 +
        0770714106936241825900018470803209931450819489958934529206669145062049) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 467 = 290 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 1 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
