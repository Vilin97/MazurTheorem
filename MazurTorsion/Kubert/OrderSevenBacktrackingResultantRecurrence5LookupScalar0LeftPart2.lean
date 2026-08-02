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

private theorem recurrence5Scalar0Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (356 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_356 :
    recurrence5Scalar0Left.coeff 356 =
      -(((((1540805000385634063514866021003986082829947 * 10 ^ 70 +
        5769698562360845862891265260205034811630965111386726890651981444748062) * 10 ^ 70 +
        9024911722705909388964166392219002201485308165525054962864639458789309) * 10 ^ 70 +
        6307565048600901341773878861860693456687624207250513671711170341423641) * 10 ^ 70 +
        5477707783068228115391762757669961051036782520311692382705099940590495) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 180 +
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
    rw [show 81 = 15 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (357 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_357 :
    recurrence5Scalar0Left.coeff 357 =
      -(((((1815659278641657925979496664888516034959822 * 10 ^ 70 +
        6922891205772452812215337310339373462000792750247270416892886564400351) * 10 ^ 70 +
        8197293676793398149661697699006069413036383379457620671973146264396874) * 10 ^ 70 +
        6282777633121359946872032473639233807315036960117889413715878597713297) * 10 ^ 70 +
        5748794193717905466699402675048502265878850121775146612964150775031266) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 181 +
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
    rw [show 81 = 14 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (358 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_358 :
    recurrence5Scalar0Left.coeff 358 =
      (((((1353463885365118436181181340611623211730901 * 10 ^ 70 +
        8445681008002356764927026732466218474790323652951415715174719730034413) * 10 ^ 70 +
        6319387368213279900002891536859820933224833385654770562253596253486120) * 10 ^ 70 +
        8218388519048539723324346786155295277280825126545508998342209218867123) * 10 ^ 70 +
        5612004119566806972878147891711226334795678422765502185531552302181401) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 182 +
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
    rw [show 81 = 13 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (359 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_359 :
    recurrence5Scalar0Left.coeff 359 =
      -(((((688957574088480514798097237898299403684682 * 10 ^ 70 +
        0786850383103898675153804509683026307599372004585536010962315759195390) * 10 ^ 70 +
        8487590425748486787333853808475891432393738260344582364564129550249428) * 10 ^ 70 +
        4231019296520805224288545535361961624331486883451219615824245983404155) * 10 ^ 70 +
        5596812229731986938493815507775818533297879280300147264581752672761205) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 183 +
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
    rw [show 81 = 12 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (360 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_360 :
    recurrence5Scalar0Left.coeff 360 =
      (((((304861209917412323380202766367609967398767 * 10 ^ 70 +
        3360032716290459012196691552182336306909643687761054912822204711378375) * 10 ^ 70 +
        9736351556111163703300499968197670523150617888741346555711972043849675) * 10 ^ 70 +
        6481771524423060087377039104549923075754323751958283636051570134378767) * 10 ^ 70 +
        3475541938104324216817797468736083985861593664109186357650559841574226) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 184 +
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
    rw [show 81 = 11 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (361 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_361 :
    recurrence5Scalar0Left.coeff 361 =
      -(((((125384011508318965194911409329421733644556 * 10 ^ 70 +
        9681187899355391983617118850811744120422710520222271749149690911419036) * 10 ^ 70 +
        4269590583058933752323941048095468408345390008444302182655136012379027) * 10 ^ 70 +
        9085535673640153891680038706317597276084493919281588412671276630401079) * 10 ^ 70 +
        3618782539317198578159902238758041339190310500140642060420814020062636) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 185 +
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
    rw [show 81 = 10 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (362 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_362 :
    recurrence5Scalar0Left.coeff 362 =
      (((((49301602442385354758878125412915429111898 * 10 ^ 70 +
        0947749081165005302227580450564811433733025824098344125318765809006612) * 10 ^ 70 +
        9498926771442028679421548575571410497683593547745151854526157439803664) * 10 ^ 70 +
        3286225026931803841246461970504995763322677716798234376351892206387525) * 10 ^ 70 +
        2517087693557430553846491096163652604073168062990395055302783168767568) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 186 +
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
    rw [show 81 = 9 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (363 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_363 :
    recurrence5Scalar0Left.coeff 363 =
      -(((((18796240410947086937009001690393122921761 * 10 ^ 70 +
        4342864175560321263702963180221265505196529201973034575589458956566462) * 10 ^ 70 +
        1192002598173603473148838153485729780536211499142120670725243846202838) * 10 ^ 70 +
        8289595289923507215959235885448587630410141837213016249822066339270356) * 10 ^ 70 +
        3052750723509992155935253370329022700489095547538648762171293869687037) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 187 +
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
    rw [show 81 = 8 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (364 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_364 :
    recurrence5Scalar0Left.coeff 364 =
      (((((6999758519941657003841478668693695403784 * 10 ^ 70 +
        0832052995576606264424302464084996118000529511304910850897218801366304) * 10 ^ 70 +
        1953342949087557615511772697719042337781074996263502321659193999716854) * 10 ^ 70 +
        1137797574431814525130564765630290490564804541933010920500590445206936) * 10 ^ 70 +
        1297129174384139820446169966405114514647712103577395175087272144484545) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 188 +
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
    rw [show 81 = 7 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (365 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_365 :
    recurrence5Scalar0Left.coeff 365 =
      -(((((2555703711345631944565105102646743830850 * 10 ^ 70 +
        9019215782530339257724468291845265949104124921383053216692344545162691) * 10 ^ 70 +
        8417953286428150592781663219115747757839880524030809200637270908799173) * 10 ^ 70 +
        6765421924411510026550536240071265910319420462425608942293663690316848) * 10 ^ 70 +
        8981444347175130307048927206171180587574133372634388888116448948734711) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 189 +
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
    rw [show 81 = 6 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (366 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_366 :
    recurrence5Scalar0Left.coeff 366 =
      (((((916268039671982135327736237853599521555 * 10 ^ 70 +
        3974595625527336198829563159948055968240450084901342670933032837940972) * 10 ^ 70 +
        0109177612618527831330970431410247738496705290570095870284283875663694) * 10 ^ 70 +
        8984701516394193145725140203868353019935674796407899535127391052620804) * 10 ^ 70 +
        4049169590200072284853805672133683051931090653793880440736519159085392) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 190 +
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
    rw [show 81 = 5 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (367 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_367 :
    recurrence5Scalar0Left.coeff 367 =
      -(((((322650203016041235605492692294041759782 * 10 ^ 70 +
        6958061809402831351682456658873835372929403357875358791612856257721546) * 10 ^ 70 +
        7667605735750473047229489922049298054342655893340378735096849966733979) * 10 ^ 70 +
        7443283695973359262465317228371184967821765660892834346018738644233571) * 10 ^ 70 +
        7480632409700889179511939363996446982748504147689124428869252252080700) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 191 +
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
    rw [show 81 = 4 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (368 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_368 :
    recurrence5Scalar0Left.coeff 368 =
      (((((111544252854418804869496462172290678172 * 10 ^ 70 +
        9962909084071730969888234667350686736008897136625307838705004716501566) * 10 ^ 70 +
        3102222967802615629378359374547483558057801680322751995695587198017142) * 10 ^ 70 +
        0056949665383758278923073876286221192092153652740161772359248136615043) * 10 ^ 70 +
        0572934276984121498687690422914471157970304025336670296846673174045991) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 192 +
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
    rw [show 81 = 3 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (369 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_369 :
    recurrence5Scalar0Left.coeff 369 =
      -(((((37830211956728386190155804106291151918 * 10 ^ 70 +
        9285990887931121650285128873579845918875139336032750907414150635789852) * 10 ^ 70 +
        5148767103837095794100854495866221440918707608096530066177494897441443) * 10 ^ 70 +
        1197091374032649320801780930259206063723024526695337188708434962528775) * 10 ^ 70 +
        3975305150992574117857345394562939403985057350297006007116477256348324) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 193 +
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
    rw [show 81 = 2 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (370 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_370 :
    recurrence5Scalar0Left.coeff 370 =
      (((((12576020506645054277759381390511515136 * 10 ^ 70 +
        0707577018621267247633738711544527930140714007570545382020783151419167) * 10 ^ 70 +
        5233262699408719879068508785692198733060281336825113903567719709906998) * 10 ^ 70 +
        4437128005564921255034763445454857240093996979111607992952812588055624) * 10 ^ 70 +
        1449044246201732699854356911630101074730324376370765404068850163093397) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 194 +
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
    rw [show 81 = 1 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (371 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_371 :
    recurrence5Scalar0Left.coeff 371 =
      -(((((4094688112130149294089409108340039914 * 10 ^ 70 +
        3000228117507362016264581612473238807716404872424573838906237695236816) * 10 ^ 70 +
        9270704708500755004758865093804501432579843004408471349710340970316801) * 10 ^ 70 +
        2429336179273091667343442926860968954883361103173182862556546785118829) * 10 ^ 70 +
        9291551344463701125018465112358642611742850998959031623802783430284528) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 195 +
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
  rw [recurrence5Scalar0Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (372 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_372 :
    recurrence5Scalar0Left.coeff 372 =
      (((((1304905552068871030691527782729345242 * 10 ^ 70 +
        2562800783549824240946450561605809427644344251992582846819780365224987) * 10 ^ 70 +
        3258789484641439266535842946284750072963065946331884459803173422029406) * 10 ^ 70 +
        0344321652693923917441464237403849247672017928930857234405427553610409) * 10 ^ 70 +
        6717909606506025563443908633457886355245710667341232474993589861588044) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 196 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 31 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (373 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_373 :
    recurrence5Scalar0Left.coeff 373 =
      -(((((406792395880018581147310759672761348 * 10 ^ 70 +
        6326785862264079560842391180700326955163246087933253110373106628395636) * 10 ^ 70 +
        9531328773122642864906511647371788058313031667499291476308889356907233) * 10 ^ 70 +
        8784292188355688138401658653087732016826891977149017148879421096902266) * 10 ^ 70 +
        6661782610747927865364273661173138114589477238223837153254527399851976) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 197 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 30 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (374 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_374 :
    recurrence5Scalar0Left.coeff 374 =
      (((((123990612484345002914266670012796284 * 10 ^ 70 +
        8337124523116711629603163620578431205427758479076063782990472341915087) * 10 ^ 70 +
        2971820321109237766245941363121958287505100465778726086349827606446463) * 10 ^ 70 +
        7099863673226697399657636937398751610841598019080636432622738827964103) * 10 ^ 70 +
        0459871310805153393956604725114197911159432622510048370349187125469983) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 198 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 29 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (375 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_375 :
    recurrence5Scalar0Left.coeff 375 =
      -(((((36933550703999210446091307621164827 * 10 ^ 70 +
        5185906630983483220923996856682426204272669761486319069344258398783900) * 10 ^ 70 +
        1139507559637086823123328834865047293468756932070058993117278850258863) * 10 ^ 70 +
        8343736630818686709044902357698590196022506978194461824302324089584149) * 10 ^ 70 +
        5484806662828600055891742810638032977184080251887772510215353700020287) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 199 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 28 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (376 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_376 :
    recurrence5Scalar0Left.coeff 376 =
      (((((10745876239378985830643536806465516 * 10 ^ 70 +
        2134384043575172718157409254288376233960382882632998925999263023032382) * 10 ^ 70 +
        2935409116803395641063024023493733372854264871876539870432585916784838) * 10 ^ 70 +
        0619029709772504298192014776347717264866833666077181419436567023817673) * 10 ^ 70 +
        1720496167145368795915769253109017533785651916825665923020913761907232) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 200 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 27 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (377 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_377 :
    recurrence5Scalar0Left.coeff 377 =
      -(((((3051907623375107533111087486654951 * 10 ^ 70 +
        5917938187679537901901081682496314989012693560784996833386203457832890) * 10 ^ 70 +
        3285259651412148601511709950975291001448202281840086717297382135566493) * 10 ^ 70 +
        2866028164290380684407327757356110986568552197543486224495053965928218) * 10 ^ 70 +
        5703569318543869435345358480013222864408635262566202738303417050683344) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 201 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 26 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (378 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_378 :
    recurrence5Scalar0Left.coeff 378 =
      (((((845374394577836549228254283439225 * 10 ^ 70 +
        7911904506057124378891306304879731089077208539243904363728967824692276) * 10 ^ 70 +
        6455672359819513938927519577552395000074305610262600591908674136903803) * 10 ^ 70 +
        0431343834956702676143060860504448062116427393110502655626178125540425) * 10 ^ 70 +
        5232858873639978203614811034548006470578528394199881001893442302391560) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 202 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 25 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (379 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_379 :
    recurrence5Scalar0Left.coeff 379 =
      -(((((228142720466314975797491721477142 * 10 ^ 70 +
        6201295798164487451179886368772127387274582877673707721731348280345127) * 10 ^ 70 +
        7104016260937621696488908253376428737368077163725619184330705423890709) * 10 ^ 70 +
        5721523814554652725320567744252773908098422383151839644141882216250981) * 10 ^ 70 +
        2640908117124440321085835197838112498620047630436237259053363569524394) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 203 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 24 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (380 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_380 :
    recurrence5Scalar0Left.coeff 380 =
      (((((59902024412164280868922745051441 * 10 ^ 70 +
        1043860657117500888296550021811726229524199808003364098365222492867778) * 10 ^ 70 +
        4483067369672147789882477283400248817838928351153682072044371682489146) * 10 ^ 70 +
        5232391705977502388568669965568443352742908764866237575811637469708271) * 10 ^ 70 +
        7329024649237506271961914248819774374335217353917884938809546196660085) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 204 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 23 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (381 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_381 :
    recurrence5Scalar0Left.coeff 381 =
      -(((((15275153434852621059394750948168 * 10 ^ 70 +
        2976172684299868832639589034404625291372975950170696496864754186177981) * 10 ^ 70 +
        3377967190559636281510240833039043308887843982836983679960306435417777) * 10 ^ 70 +
        1854616879425067165186679068258027622912855238777946261298652713038276) * 10 ^ 70 +
        9296857692426916351307567819062166772453082051107088503231895081570326) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 205 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 22 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (382 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_382 :
    recurrence5Scalar0Left.coeff 382 =
      (((((3774476815967365227310632922531 * 10 ^ 70 +
        8176720713002251963958692644057072784857690729803370060876293273515647) * 10 ^ 70 +
        4791892299740124955447514748663766277293693996169068057396389164996192) * 10 ^ 70 +
        8836773264866012424934054557455925060107526517819605090865751223779178) * 10 ^ 70 +
        2466661756004660793921613573374217238227984435213349829780484735150231) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 206 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 21 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (383 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_383 :
    recurrence5Scalar0Left.coeff 383 =
      -(((((901101107555653409413272110049 * 10 ^ 70 +
        6369321556870503223051448053247920940888600939716425366880635387245164) * 10 ^ 70 +
        2919508459332956114412936493537285467668518253463955214306305411224489) * 10 ^ 70 +
        8574155170970800217757740449177118221014609181684365540926292117458572) * 10 ^ 70 +
        8481414925291715970648131888560559189294622805364470051069408665271956) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 207 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 20 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (384 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_384 :
    recurrence5Scalar0Left.coeff 384 =
      (((((207012551038687503720402330860 * 10 ^ 70 +
        1775616887705404597863771332252167542214976938959120261700764125951930) * 10 ^ 70 +
        5422003689245262275123886533576095157622073337728230338061833758775559) * 10 ^ 70 +
        9919046971574009592705202733282641053026635034832941329068513005095220) * 10 ^ 70 +
        5667853958026132947504121879972831346170300138568296295761612112807646) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 208 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 19 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (385 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_385 :
    recurrence5Scalar0Left.coeff 385 =
      -(((((45502271386187117492505245136 * 10 ^ 70 +
        7137932135962571507897481044800557599904570925051210704164080045866135) * 10 ^ 70 +
        4935687983948153892520778495953292186991686030192524397866954641948203) * 10 ^ 70 +
        7121106659395311991038756601143336890924741671004237706765847430496752) * 10 ^ 70 +
        5749890288331787931177363614213338145506541436603508684636589562867365) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 209 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 18 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (386 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_386 :
    recurrence5Scalar0Left.coeff 386 =
      (((((9485562545793221105745987845 * 10 ^ 70 +
        7705252300027959009101231739957400381397143412745776259709056906213166) * 10 ^ 70 +
        6665412209815153072522204535914326761664608374451863978598384137155390) * 10 ^ 70 +
        2404750371493658880050046154924054081144647741453911357754832760324011) * 10 ^ 70 +
        7701077273024084329067309175875863579077020783957537495275630255240890) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 210 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 17 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (387 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_387 :
    recurrence5Scalar0Left.coeff 387 =
      -(((((1848158875800138543919443143 * 10 ^ 70 +
        7918474654567270726672795647409971702943582703131548995245521087922377) * 10 ^ 70 +
        8667193022614297121616797083816554854570651161340349382626848224679328) * 10 ^ 70 +
        1245702995285132598846483991531950641462456484798526972187517259258934) * 10 ^ 70 +
        8582066943392129754794759305200916434330991658191716892509427361025202) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 211 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 16 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (388 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_388 :
    recurrence5Scalar0Left.coeff 388 =
      (((((327527585411735157998896220 * 10 ^ 70 +
        9932636582766460307919672440373218560551932108060269736570457904429094) * 10 ^ 70 +
        4828049745596397900456981224009877694432862925724526646982927385018334) * 10 ^ 70 +
        3790637766613996169899511686996314392772056812263166945231337749868056) * 10 ^ 70 +
        5730891611602796400912182030788605938473361972006020334991697580639990) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 212 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 15 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (389 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_389 :
    recurrence5Scalar0Left.coeff 389 =
      -(((((49665128867026877080791740 * 10 ^ 70 +
        0027285751977376919029651475962627883660595422254608601084970981112206) * 10 ^ 70 +
        9116132797422911979874055224398182396824349354592390502224940517981256) * 10 ^ 70 +
        8888967856549570064686732773263072018637586333212233637389083935355921) * 10 ^ 70 +
        7711424073046618790038009687811065621482393101024311747557382568721821) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 213 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 14 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (390 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_390 :
    recurrence5Scalar0Left.coeff 390 =
      (((((5262613830712821571980240 * 10 ^ 70 +
        9747284196609349276541479010331234220288709628338302535296227958924027) * 10 ^ 70 +
        4926803754760854585639228500603225362166172503713310138715142005532705) * 10 ^ 70 +
        7624775013636339770499979372151099804960750261315779629748637899821769) * 10 ^ 70 +
        8107135318559708023824248928994278086193773882393292501022816037471467) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 214 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 13 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (391 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_391 :
    recurrence5Scalar0Left.coeff 391 =
      (((((136006340570262784507312 * 10 ^ 70 +
        1343446769709968673258046845799836485240518699684551098824675285946579) * 10 ^ 70 +
        0119152997774895012112156225533439452174417805239254464744897683023913) * 10 ^ 70 +
        9418603172929373132882467052487578152559174664047052459777477254967547) * 10 ^ 70 +
        8625608255671688323058604910223238979501795208505712278633276193573705) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 215 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 12 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (392 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_392 :
    recurrence5Scalar0Left.coeff 392 =
      -(((((294848851187174499588302 * 10 ^ 70 +
        1498999088537033471154129939299849128012481019594865197111711545889278) * 10 ^ 70 +
        0522076933076157484514935718924520598490073007349022377824669836357959) * 10 ^ 70 +
        0773383701156633630135967930622071600981447352286588196580953335348999) * 10 ^ 70 +
        4128600932059008160605998356577306291233408129062976026342557221501895) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 216 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 11 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (393 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_393 :
    recurrence5Scalar0Left.coeff 393 =
      (((((112009145826056682958586 * 10 ^ 70 +
        2028824864998847343976881254389358337003149690148964414154541941745778) * 10 ^ 70 +
        7943625801945892557050335208876905156543157203995641298752750466845723) * 10 ^ 70 +
        6048281989571834868990183462312535667293699568427930576802847522072818) * 10 ^ 70 +
        2779502495948473484609579218841836152741198898595360054170110357478445) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 217 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 10 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (394 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_394 :
    recurrence5Scalar0Left.coeff 394 =
      -(((((31254571878151872040396 * 10 ^ 70 +
        6494418624319171848600081410278197707918897103990561243350324802991986) * 10 ^ 70 +
        0717253530870069950825804406496630443583835613226232254815608609601928) * 10 ^ 70 +
        5033796116351134923346921746154569352228470633752658168414770691598264) * 10 ^ 70 +
        8822473453532894827072630144358569540984458139883334787510409657824745) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 395 = 218 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 9 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (395 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_395 :
    recurrence5Scalar0Left.coeff 395 =
      (((((7296017637712472233124 * 10 ^ 70 +
        4716067671590047032075971679583550363393034604100884463616070704983708) * 10 ^ 70 +
        9752828775247440386639110668664561138550073312958267747933475857466726) * 10 ^ 70 +
        4002780387590221936703098507774816698018001420806020718720747985852451) * 10 ^ 70 +
        1201139945546269991242181873408716548779978817554514320172265680601701) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 396 = 219 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 8 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (396 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_396 :
    recurrence5Scalar0Left.coeff 396 =
      -(((((1446935983688843014039 * 10 ^ 70 +
        5317423184424776884698315180636429612056358334502222623255307969449447) * 10 ^ 70 +
        9624844530895260592739067686834065903869000735246274827151183367565092) * 10 ^ 70 +
        9841049905154281381872961431562184334655683670727156738681543681095949) * 10 ^ 70 +
        1304576941017382614846265932081946709182557756114585807660643393287231) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 397 = 220 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 7 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (397 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_397 :
    recurrence5Scalar0Left.coeff 397 =
      (((((229578432876541533714 * 10 ^ 70 +
        2094389027386811175917857151962082698495764830316656243151668813311167) * 10 ^ 70 +
        0465486714017425838731925812331011047888658809330081085176462964678716) * 10 ^ 70 +
        7911103731678967280380574785225691161603600702273296468597470355774793) * 10 ^ 70 +
        9389245839809891632642925598622186087044636017907570188209034612620719) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 398 = 221 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 6 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (398 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_398 :
    recurrence5Scalar0Left.coeff 398 =
      -(((((21233876159234750250 * 10 ^ 70 +
        9163818290587059043647143917282513943566005189740817466058300933247051) * 10 ^ 70 +
        6724830139943930699507924076121935128186251189715619218356011443225710) * 10 ^ 70 +
        2782246961698140308962784803429896531401854594307295700988371979280084) * 10 ^ 70 +
        8557070800946557272126777909782756599943066043127804610298920119283025) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 399 = 222 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 5 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (399 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_399 :
    recurrence5Scalar0Left.coeff 399 =
      -(((((2909482485363432879 * 10 ^ 70 +
        6136864208183535404537066289001199026366928702413317427094611290497611) * 10 ^ 70 +
        1566418859354725353285732508697380769393245124732774842544740408587821) * 10 ^ 70 +
        3399897226971836656196959266329911391395577320957734847589153373821275) * 10 ^ 70 +
        8225639663515525292477122442775124098130296190292544670520089314821924) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 400 = 223 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 4 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (400 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_400 :
    recurrence5Scalar0Left.coeff 400 =
      (((((2217718700306103721 * 10 ^ 70 +
        1960088871054815676642030914975966802231567847410658852440952277070459) * 10 ^ 70 +
        7220801545115686911861407162564609674958231741493417429696490220239678) * 10 ^ 70 +
        6207184529456884237370882022941095147424588687969412458071025090146388) * 10 ^ 70 +
        2169776241961281578810449547001801758292803473390264551688681099951131) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 401 = 224 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 3 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (401 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_401 :
    recurrence5Scalar0Left.coeff 401 =
      -(((((727683483237032676 * 10 ^ 70 +
        4533540029307137371863102102950236676006739669800478442321108049818909) * 10 ^ 70 +
        5180806920719022604059544576644828324662422855385560868995371704913118) * 10 ^ 70 +
        4622183400926542552696493995773025334395705848292033987787319329290486) * 10 ^ 70 +
        8512342133125259467579227766290080025348494298328053448966244970557237) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 402 = 225 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 2 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (402 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_402 :
    recurrence5Scalar0Left.coeff 402 =
      (((((173914032170359835 * 10 ^ 70 +
        7121772144066081566601351824573156359650693195442269781713059822328798) * 10 ^ 70 +
        7048289719701236031488681945791107656135477774262749834649147286978602) * 10 ^ 70 +
        8214098517523302414471202530472833036126601705604180899446630688574388) * 10 ^ 70 +
        6839554818266950381424760342701484520307174823987810426010906184800482) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 403 = 226 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 1 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (403 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_403 :
    recurrence5Scalar0Left.coeff 403 =
      -(((((31885779798189254 * 10 ^ 70 +
        7381708868745506220338936569040179645520778449416690331186627282146956) * 10 ^ 70 +
        8251448492471197563564301417809328346198983423962070246196794788431550) * 10 ^ 70 +
        7751248609479311402797641064050953419507627036822035505983824915676002) * 10 ^ 70 +
        8513662551859425506346453078698831860149048912229512945465382316614268) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 404 = 227 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (404 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_404 :
    recurrence5Scalar0Left.coeff 404 =
      (((((4083962981095450 * 10 ^ 70 +
        9142967115470291449225012044678246725527270077362836118751517670726476) * 10 ^ 70 +
        4388391272829379598435410413762543967787709433394709110994790280835796) * 10 ^ 70 +
        1954266394171489259132945569387734848088804808915000726768048139709107) * 10 ^ 70 +
        1805361272061886857661833646060855425681105279692613801644004260552335) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 405 = 228 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 31 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (405 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_405 :
    recurrence5Scalar0Left.coeff 405 =
      -(((((157712514171659 * 10 ^ 70 +
        3488760909625478955171186738209029361057385902121509507044370461023297) * 10 ^ 70 +
        3565944683097365369285965950653248916340195355072595185100368791424924) * 10 ^ 70 +
        1241512413515960766851878280348948362880477023648706498479182313842890) * 10 ^ 70 +
        5642501876087134241958027611038207961682456035742557259904976279909900) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 406 = 229 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 30 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (406 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_406 :
    recurrence5Scalar0Left.coeff 406 =
      -(((((93605040637235 * 10 ^ 70 +
        0479128913989192377560921264867985098903053518022852095084870398019450) * 10 ^ 70 +
        7262666696092494430384933364372025437810367801296266577274704277837052) * 10 ^ 70 +
        5403808945961166625077036046397999749034349612153210276337628735492997) * 10 ^ 70 +
        5545513593837457596734149165073643026469010227038775565196742887278676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 407 = 230 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 29 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (407 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_407 :
    recurrence5Scalar0Left.coeff 407 =
      (((((33815162244272 * 10 ^ 70 +
        7451641494702031246126984599716757210460389353813508758956195264142190) * 10 ^ 70 +
        2737238885623860708170618069230257878263367746584223622542809236809149) * 10 ^ 70 +
        2887390360304360409508284483679992280766273106117504517490083435773891) * 10 ^ 70 +
        8661939494929931112420836730130054768869967928128110236530936469584803) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 408 = 231 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 28 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (408 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_408 :
    recurrence5Scalar0Left.coeff 408 =
      -(((((7061474289590 * 10 ^ 70 +
        2610821083699713490259124417723726358539770117189007022780006062987749) * 10 ^ 70 +
        7122660353602284555119052869587165923948603811572746513252383468763433) * 10 ^ 70 +
        6508377885701753512479348309697656606426526031551011020460648488455827) * 10 ^ 70 +
        0472986651893834724401832254422942130029084318135379555644903441479667) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 409 = 232 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 27 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (409 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_409 :
    recurrence5Scalar0Left.coeff 409 =
      (((((1029872966912 * 10 ^ 70 +
        6296382449249277899264551311016924574555419754176922227571722516128969) * 10 ^ 70 +
        5437118328121070207478686430753648694524362717326851667671107938427889) * 10 ^ 70 +
        9477350209753963222478769371134480972250490246632977601372281353153217) * 10 ^ 70 +
        9414656423006167547469621147343697506066219704849135409118991750179374) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 410 = 233 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 26 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (410 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_410 :
    recurrence5Scalar0Left.coeff 410 =
      -(((((92865929598 * 10 ^ 70 +
        0400599713257677854349590050744368288217193266649429572476250851916453) * 10 ^ 70 +
        6474557531719245722031219932879773305505230722823364010866995695646093) * 10 ^ 70 +
        9854100258863312510332391479747332134634521130529821755467771390594719) * 10 ^ 70 +
        7416377611676288773742656950378324629753468699148493836375909823879797) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 411 = 234 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 25 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (411 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_411 :
    recurrence5Scalar0Left.coeff 411 =
      -(((((1152200656 * 10 ^ 70 +
        3881802288937651878840302391971708018014845064345799038945646746813725) * 10 ^ 70 +
        9182873912017559509592893165195770704820295231640517945453547665816503) * 10 ^ 70 +
        1245570480512740668032149507708713338123659856246562965516402206246174) * 10 ^ 70 +
        4797871442604470131951907685614434191209542531120922065168530749450007) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 412 = 235 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 24 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (412 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_412 :
    recurrence5Scalar0Left.coeff 412 =
      (((((2524651511 * 10 ^ 70 +
        4130074554570111952283289485971518826873394101903998687211430260390460) * 10 ^ 70 +
        1722257029663482119323428992393624974466972412848520711815724742180788) * 10 ^ 70 +
        8287189973696206286246186523949204858977084002467692172931451043259457) * 10 ^ 70 +
        6215087939845551804301141685800238802319294783343044514154642152500749) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 413 = 236 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 23 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (413 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_413 :
    recurrence5Scalar0Left.coeff 413 =
      -(((((638310567 * 10 ^ 70 +
        6122092340130939485871303338035216917127282951545208967555709972057015) * 10 ^ 70 +
        0814954586266498654614933237857028968423117441787774966241476305574111) * 10 ^ 70 +
        5321422040409743629871567445224286386895748252023936766942886721421176) * 10 ^ 70 +
        0490101822494893283514395398140706697201471991215408627460489558247022) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 414 = 237 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 22 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (414 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_414 :
    recurrence5Scalar0Left.coeff 414 =
      (((((113827928 * 10 ^ 70 +
        0225432001097598550923196681209563380143905863401611403624787321275968) * 10 ^ 70 +
        9103888784320746046604251876633355395953918852719214313666203378631211) * 10 ^ 70 +
        4884099639041410232523648433473199620753717459138323642551892825026785) * 10 ^ 70 +
        0716210572063767096350125666377231821088429559100432828333267371643259) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 415 = 238 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 21 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (415 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_415 :
    recurrence5Scalar0Left.coeff 415 =
      -(((((16901583 * 10 ^ 70 +
        8695856372281827412129982618241077394149711198589395472782505509468782) * 10 ^ 70 +
        9965409011616218797995273889430164028658990332830997051402703933954266) * 10 ^ 70 +
        2583517360326776795598047801148249695307338403603793342766939981194683) * 10 ^ 70 +
        9038314185420151957015023396626191781788538654526119379122768031139370) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 416 = 239 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 20 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (416 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_416 :
    recurrence5Scalar0Left.coeff 416 =
      (((((2174900 * 10 ^ 70 +
        1496857954204612922369599158850109340938202168592692127735727568715722) * 10 ^ 70 +
        4532941644610152606285257674353768667552840798186844760193293105457390) * 10 ^ 70 +
        5586189648684935306586955102447920074337695105790226386327916834060155) * 10 ^ 70 +
        6414882894426311484898167376527865949338931016928073247271335747842083) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 417 = 240 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 19 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (417 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_417 :
    recurrence5Scalar0Left.coeff 417 =
      -(((((233966 * 10 ^ 70 +
        4174573487741795494116832407489896351034040097147296518060123877510571) * 10 ^ 70 +
        8424710578264653169024583908147017823708748887103712037760960005445002) * 10 ^ 70 +
        5775260290463826810613995783311729296162175577945873413661025315564564) * 10 ^ 70 +
        4179716141619744995087458237974654126907710072883911724662382183250003) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 418 = 241 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 18 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (418 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_418 :
    recurrence5Scalar0Left.coeff 418 =
      (((((17861 * 10 ^ 70 +
        8708964405125674189008049774955270488179650577042314648338252185388261) * 10 ^ 70 +
        8794906192433271596139300497502336662082276157031157723513063422360532) * 10 ^ 70 +
        7946394753931508437280371411018154667925627948545501682598737695782736) * 10 ^ 70 +
        1865699270792094936429486867486973869961599690823740784941023320458220) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 419 = 242 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 17 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (419 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_419 :
    recurrence5Scalar0Left.coeff 419 =
      -(((((232 * 10 ^ 70 +
        1660204892691531715173329844636584496180951636172405353911856726899473) * 10 ^ 70 +
        6739195481377220588377193474454473323013865734973001930007620730713257) * 10 ^ 70 +
        3132087410225437115444520658756059002974572306465232004891814124615084) * 10 ^ 70 +
        7311044070060553753670657075882866422644097145697144571504705465727705) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 420 = 243 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 16 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (420 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_420 :
    recurrence5Scalar0Left.coeff 420 =
      -(((((197 * 10 ^ 70 +
        8200262486286069092134800221371422837986768170409350330287656013608682) * 10 ^ 70 +
        1764299856430234317916101911849498711417741337579326487771844651637589) * 10 ^ 70 +
        2417855319137439337635061147566220378435835074842225021894897575930299) * 10 ^ 70 +
        7456832264315565960551245348619778870626275583096336341397185456249746) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 421 = 244 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 15 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (421 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_421 :
    recurrence5Scalar0Left.coeff 421 =
      (((((36 * 10 ^ 70 +
        4890137481063994888412403212589097957763927210744442127495334101928890) * 10 ^ 70 +
        7643966643712568217093146847390368625498062002483803137976740647595469) * 10 ^ 70 +
        8025357088380804978809296896790807487424143286221904782756839890798713) * 10 ^ 70 +
        1713225400411325866049823502195084846646555705817891414918794568169908) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 422 = 245 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 14 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (422 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_422 :
    recurrence5Scalar0Left.coeff 422 =
      -(((((3 * 10 ^ 70 +
        4365778350905829730755730600709179055766524279480419954680569984460396) * 10 ^ 70 +
        6747923350007900324327674123410194348844229756677144467557620334452126) * 10 ^ 70 +
        9281038516045835778375245448419474364722086815557725415227251896891017) * 10 ^ 70 +
        6342089070620044681572993679348160802145567389071810931564494055125146) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 423 = 246 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 13 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (423 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_423 :
    recurrence5Scalar0Left.coeff 423 =
      ((((1210097005709893494907305570256606545556577456662755199581528966710780 * 10 ^ 70 +
        7596848197467726388818065794700965604915740819232025160909762890191946) * 10 ^ 70 +
        2309308537974618071238347204372486585254660473760432127023164358569144) * 10 ^ 70 +
        6102989389550981392813646337828908718161310361096265013414484490108023) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 424 = 247 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 12 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (424 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_424 :
    recurrence5Scalar0Left.coeff 424 =
      ((((141015528194102200610086077528394466247982954555789585131781033917027 * 10 ^ 70 +
        5512419019505986470025919727045529776711398962145954446192462244067037) * 10 ^ 70 +
        0385910064024094712860012708096040987508233211353969229396171572462769) * 10 ^ 70 +
        6252343593479703908756242965837015559577355158824426329399541429045623) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 425 = 248 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 11 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (425 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_425 :
    recurrence5Scalar0Left.coeff 425 =
      -((((24046525455483726455406566125683451918486869628119881878380072865257 * 10 ^ 70 +
        5101583203743148900737325938215546971294853597703826877660164383662087) * 10 ^ 70 +
        5633374405310968357677318457857374112651013861433297785775663268595054) * 10 ^ 70 +
        5996079688874844785136512390513186120575371127248491244242569954519364) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 426 = 249 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 10 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (426 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_426 :
    recurrence5Scalar0Left.coeff 426 =
      ((((1388833997720180666905220176758805983601227461579994623685779935505 * 10 ^ 70 +
        4192762797743440741587677430723566518634060651080553233407026252123043) * 10 ^ 70 +
        1058508406311071809544257455405142575910463630545294723306424889726493) * 10 ^ 70 +
        7633512360852601555543765547345000812934489623007874291733191778624824) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 427 = 250 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 9 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (427 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_427 :
    recurrence5Scalar0Left.coeff 427 =
      ((((14454541632932519951000980401653042318661867253225974146145929312 * 10 ^ 70 +
        1542697311739197078505698381876879591088984047370581365620585929288769) * 10 ^ 70 +
        1746972842151223364964027223313514196154758634966833222374983854162968) * 10 ^ 70 +
        8075684877460009815426084589993925772284436362249819596281193460314215) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 428 = 251 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 8 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (428 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_428 :
    recurrence5Scalar0Left.coeff 428 =
      -((((7169067624637569583178166895701488122696389775696959505065815601 * 10 ^ 70 +
        5759816561682405615044153395224353872780491544417325534417643851279529) * 10 ^ 70 +
        1961624213786843828356656685876500095131213239916226963371586116902707) * 10 ^ 70 +
        3155117220832214457402291617184522984375577037536616359888779576080111) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 429 = 252 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 7 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (429 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_429 :
    recurrence5Scalar0Left.coeff 429 =
      ((((357724589051188181488435227340176119557469604182557866855338722 * 10 ^ 70 +
        4642269943358587532544944847258384228986216621307908558570102405031788) * 10 ^ 70 +
        5565168508014561125346339444063247887646666535757906110479049266840218) * 10 ^ 70 +
        2993571885098097556460351341283645757829992825797029416841118496160198) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 430 = 253 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 6 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (430 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_430 :
    recurrence5Scalar0Left.coeff 430 =
      ((((4499177402060529411627715808180107102223629980381684020419833 * 10 ^ 70 +
        8300573342523398262234528565515498704883942254372933783126825462613642) * 10 ^ 70 +
        1154864673946967891627111872626973252413773011750893339388591222669204) * 10 ^ 70 +
        3561764842338332292245213742548428429129783262965425414872452090659721) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 431 = 254 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 5 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (431 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_431 :
    recurrence5Scalar0Left.coeff 431 =
      -((((937841017244245965529205845239786560750266111606270387676667 * 10 ^ 70 +
        8335471288941764693850662040494806574408167983342166097899118456338884) * 10 ^ 70 +
        8690673371732107735489595409575073107846099977288265688847101123252366) * 10 ^ 70 +
        1955874694147553786245720107856903280425199271542013335622008215419695) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 255 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 4 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (432 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_432 :
    recurrence5Scalar0Left.coeff 432 =
      ((((11081085625433426905522862217341566829825466887676675910630 * 10 ^ 70 +
        9280378822287726050174365469604627470798355077047666999981509186600729) * 10 ^ 70 +
        8602291139337548957953678923078199161145130839954394789649646209201544) * 10 ^ 70 +
        0518719925758986682395692092569522504843432911500370127267718669429632) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 256 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 3 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (433 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_433 :
    recurrence5Scalar0Left.coeff 433 =
      ((((1139651947579055546376003330673182612617132655447692033505 * 10 ^ 70 +
        8580159922077179099604606408336246314760528427354974197140201928389192) * 10 ^ 70 +
        8855834757264716190325949813859751240689922028527823087995604163049287) * 10 ^ 70 +
        2304801407515718801484908130209928206657005049177218650205377319429441) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 257 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 2 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (434 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_434 :
    recurrence5Scalar0Left.coeff 434 =
      -((((11278622389481156858521458343226713891545437557763874469 * 10 ^ 70 +
        8075626617621888618862282963009487180455738143938693365536733296999704) * 10 ^ 70 +
        9760884136027376297586516085674496688038501039311985573337832632046436) * 10 ^ 70 +
        4245982201737312536043352075870896748220196045882727358761781683708813) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 258 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 1 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Left_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (435 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_435 :
    recurrence5Scalar0Left.coeff 435 =
      -((((882903559521579243531370917526574745915813999481956905 * 10 ^ 70 +
        1918304764341073743058356521062912439880727534765182970354223757012552) * 10 ^ 70 +
        6605811401021930006220541261654677276726757402158455264805154403157337) * 10 ^ 70 +
        4278763811980571539285434940856876335381908844933266355163008134028281) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 259 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
