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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
