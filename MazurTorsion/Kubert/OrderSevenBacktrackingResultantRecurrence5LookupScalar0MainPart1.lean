/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B0_coeff_0
  recurrence5B0_coeff_1
  recurrence5B0_coeff_2
  recurrence5B0_coeff_3
  recurrence5B0_coeff_4
  recurrence5B0_coeff_5
  recurrence5B0_coeff_6
  recurrence5B0_coeff_7
  recurrence5B0_coeff_8
  recurrence5B0_coeff_9
  recurrence5B0_coeff_10
  recurrence5B0_coeff_11
  recurrence5B0_coeff_12
  recurrence5B0_coeff_13
  recurrence5B0_coeff_14
  recurrence5B0_coeff_15
  recurrence5B0_coeff_16
  recurrence5B0_coeff_17
  recurrence5B0_coeff_18
  recurrence5B0_coeff_19
  recurrence5B0_coeff_20
  recurrence5B0_coeff_21
  recurrence5B0_coeff_22
  recurrence5B0_coeff_23
  recurrence5B0_coeff_24
  recurrence5B0_coeff_25
  recurrence5B0_coeff_26
  recurrence5B0_coeff_27
  recurrence5B0_coeff_28
  recurrence5B0_coeff_29
  recurrence5B0_coeff_30
  recurrence5B0_coeff_31
  recurrence5B0_coeff_32
  recurrence5B0_coeff_33
  recurrence5B0_coeff_34
  recurrence5B0_coeff_35
  recurrence5B0_coeff_36
  recurrence5B0_coeff_37
  recurrence5B0_coeff_38
  recurrence5B0_coeff_39
  recurrence5B0_coeff_40
  recurrence5B0_coeff_41
  recurrence5B0_coeff_42
  recurrence5B0_coeff_43
  recurrence5B0_coeff_44
  recurrence5B0_coeff_45
  recurrence5B0_coeff_46
  recurrence5B0_coeff_47
  recurrence5B0_coeff_48
  recurrence5B0_coeff_49
  recurrence5B0_coeff_50
  recurrence5B0_coeff_51
  recurrence5B0_coeff_52
  recurrence5B0_coeff_53
  recurrence5B0_coeff_54
  recurrence5B0_coeff_55
  recurrence5B0_coeff_56
  recurrence5B0_coeff_57
  recurrence5B0_coeff_58
  recurrence5B0_coeff_59
  recurrence5B0_coeff_60
  recurrence5B0_coeff_61
  recurrence5B0_coeff_62
  recurrence5B0_coeff_63

attribute [local simp]
  recurrence5B0_coeff_64
  recurrence5B0_coeff_65
  recurrence5B0_coeff_66
  recurrence5B0_coeff_67
  recurrence5B0_coeff_68
  recurrence5B0_coeff_69
  recurrence5B0_coeff_70
  recurrence5B0_coeff_71
  recurrence5B0_coeff_72
  recurrence5B0_coeff_73
  recurrence5B0_coeff_74
  recurrence5B0_coeff_75
  recurrence5B0_coeff_76
  recurrence5B0_coeff_77
  recurrence5B0_coeff_78
  recurrence5B0_coeff_79
  recurrence5B0_coeff_80
  recurrence5B0_coeff_81
  recurrence5B0_coeff_82
  recurrence5B0_coeff_83
  recurrence5B0_coeff_84
  recurrence5B0_coeff_85
  recurrence5B0_coeff_86
  recurrence5B0_coeff_87
  recurrence5B0_coeff_88
  recurrence5B0_coeff_89
  recurrence5B0_coeff_90
  recurrence5B0_coeff_91
  recurrence5B0_coeff_92
  recurrence5B0_coeff_93
  recurrence5B0_coeff_94
  recurrence5B0_coeff_95
  recurrence5B0_coeff_96
  recurrence5B0_coeff_97
  recurrence5B0_coeff_98
  recurrence5B0_coeff_99
  recurrence5B0_coeff_100
  recurrence5B0_coeff_101
  recurrence5B0_coeff_102
  recurrence5B0_coeff_103
  recurrence5B0_coeff_104
  recurrence5B0_coeff_105
  recurrence5B0_coeff_106
  recurrence5B0_coeff_107
  recurrence5B0_coeff_108
  recurrence5B0_coeff_109
  recurrence5B0_coeff_110
  recurrence5B0_coeff_111
  recurrence5B0_coeff_112
  recurrence5B0_coeff_113
  recurrence5B0_coeff_114
  recurrence5B0_coeff_115
  recurrence5B0_coeff_116
  recurrence5B0_coeff_117
  recurrence5B0_coeff_118
  recurrence5B0_coeff_119
  recurrence5B0_coeff_120
  recurrence5B0_coeff_121
  recurrence5B0_coeff_122
  recurrence5B0_coeff_123
  recurrence5B0_coeff_124
  recurrence5B0_coeff_125
  recurrence5B0_coeff_126
  recurrence5B0_coeff_127

attribute [local simp]
  recurrence5B0_coeff_128
  recurrence5B0_coeff_129
  recurrence5B0_coeff_130
  recurrence5B0_coeff_131
  recurrence5B0_coeff_132
  recurrence5B0_coeff_133
  recurrence5B0_coeff_134
  recurrence5B0_coeff_135
  recurrence5B0_coeff_136
  recurrence5B0_coeff_137
  recurrence5B0_coeff_138
  recurrence5B0_coeff_139
  recurrence5B0_coeff_140
  recurrence5B0_coeff_141
  recurrence5B0_coeff_142
  recurrence5B0_coeff_143
  recurrence5B0_coeff_144
  recurrence5B0_coeff_145
  recurrence5B0_coeff_146
  recurrence5B0_coeff_147
  recurrence5B0_coeff_148
  recurrence5B0_coeff_149
  recurrence5B0_coeff_150
  recurrence5B0_coeff_151
  recurrence5B0_coeff_152
  recurrence5B0_coeff_153
  recurrence5QuotientConstant_coeff_0
  recurrence5QuotientConstant_coeff_1
  recurrence5QuotientConstant_coeff_2
  recurrence5QuotientConstant_coeff_3
  recurrence5QuotientConstant_coeff_4
  recurrence5QuotientConstant_coeff_5
  recurrence5QuotientConstant_coeff_6
  recurrence5QuotientConstant_coeff_7
  recurrence5QuotientConstant_coeff_8
  recurrence5QuotientConstant_coeff_9
  recurrence5QuotientConstant_coeff_10
  recurrence5QuotientConstant_coeff_11
  recurrence5QuotientConstant_coeff_12
  recurrence5QuotientConstant_coeff_13
  recurrence5QuotientConstant_coeff_14
  recurrence5QuotientConstant_coeff_15
  recurrence5QuotientConstant_coeff_16
  recurrence5QuotientConstant_coeff_17
  recurrence5QuotientConstant_coeff_18
  recurrence5QuotientConstant_coeff_19
  recurrence5QuotientConstant_coeff_20
  recurrence5QuotientConstant_coeff_21
  recurrence5QuotientConstant_coeff_22
  recurrence5QuotientConstant_coeff_23
  recurrence5QuotientConstant_coeff_24
  recurrence5QuotientConstant_coeff_25
  recurrence5QuotientConstant_coeff_26
  recurrence5QuotientConstant_coeff_27
  recurrence5QuotientConstant_coeff_28
  recurrence5QuotientConstant_coeff_29
  recurrence5QuotientConstant_coeff_30
  recurrence5QuotientConstant_coeff_31
  recurrence5QuotientConstant_coeff_32
  recurrence5QuotientConstant_coeff_33
  recurrence5QuotientConstant_coeff_34
  recurrence5QuotientConstant_coeff_35
  recurrence5QuotientConstant_coeff_36
  recurrence5QuotientConstant_coeff_37

attribute [local simp]
  recurrence5QuotientConstant_coeff_38
  recurrence5QuotientConstant_coeff_39
  recurrence5QuotientConstant_coeff_40
  recurrence5QuotientConstant_coeff_41
  recurrence5QuotientConstant_coeff_42
  recurrence5QuotientConstant_coeff_43
  recurrence5QuotientConstant_coeff_44
  recurrence5QuotientConstant_coeff_45
  recurrence5QuotientConstant_coeff_46
  recurrence5QuotientConstant_coeff_47
  recurrence5QuotientConstant_coeff_48
  recurrence5QuotientConstant_coeff_49
  recurrence5QuotientConstant_coeff_50
  recurrence5QuotientConstant_coeff_51
  recurrence5QuotientConstant_coeff_52
  recurrence5QuotientConstant_coeff_53
  recurrence5QuotientConstant_coeff_54
  recurrence5QuotientConstant_coeff_55
  recurrence5QuotientConstant_coeff_56
  recurrence5QuotientConstant_coeff_57
  recurrence5QuotientConstant_coeff_58
  recurrence5QuotientConstant_coeff_59
  recurrence5QuotientConstant_coeff_60
  recurrence5QuotientConstant_coeff_61
  recurrence5QuotientConstant_coeff_62
  recurrence5QuotientConstant_coeff_63
  recurrence5QuotientConstant_coeff_64
  recurrence5QuotientConstant_coeff_65
  recurrence5QuotientConstant_coeff_66
  recurrence5QuotientConstant_coeff_67
  recurrence5QuotientConstant_coeff_68
  recurrence5QuotientConstant_coeff_69
  recurrence5QuotientConstant_coeff_70
  recurrence5QuotientConstant_coeff_71
  recurrence5QuotientConstant_coeff_72
  recurrence5QuotientConstant_coeff_73
  recurrence5QuotientConstant_coeff_74
  recurrence5QuotientConstant_coeff_75
  recurrence5QuotientConstant_coeff_76
  recurrence5QuotientConstant_coeff_77
  recurrence5QuotientConstant_coeff_78
  recurrence5QuotientConstant_coeff_79
  recurrence5QuotientConstant_coeff_80
  recurrence5QuotientConstant_coeff_81
  recurrence5QuotientConstant_coeff_82
  recurrence5QuotientConstant_coeff_83
  recurrence5QuotientConstant_coeff_84
  recurrence5QuotientConstant_coeff_85
  recurrence5QuotientConstant_coeff_86
  recurrence5QuotientConstant_coeff_87
  recurrence5QuotientConstant_coeff_88
  recurrence5QuotientConstant_coeff_89
  recurrence5QuotientConstant_coeff_90
  recurrence5QuotientConstant_coeff_91
  recurrence5QuotientConstant_coeff_92
  recurrence5QuotientConstant_coeff_93
  recurrence5QuotientConstant_coeff_94
  recurrence5QuotientConstant_coeff_95
  recurrence5QuotientConstant_coeff_96
  recurrence5QuotientConstant_coeff_97
  recurrence5QuotientConstant_coeff_98
  recurrence5QuotientConstant_coeff_99
  recurrence5QuotientConstant_coeff_100
  recurrence5QuotientConstant_coeff_101

attribute [local simp]
  recurrence5QuotientConstant_coeff_102
  recurrence5QuotientConstant_coeff_103
  recurrence5QuotientConstant_coeff_104
  recurrence5QuotientConstant_coeff_105
  recurrence5QuotientConstant_coeff_106
  recurrence5QuotientConstant_coeff_107
  recurrence5QuotientConstant_coeff_108
  recurrence5QuotientConstant_coeff_109
  recurrence5QuotientConstant_coeff_110
  recurrence5QuotientConstant_coeff_111
  recurrence5QuotientConstant_coeff_112
  recurrence5QuotientConstant_coeff_113
  recurrence5QuotientConstant_coeff_114
  recurrence5QuotientConstant_coeff_115
  recurrence5QuotientConstant_coeff_116
  recurrence5QuotientConstant_coeff_117
  recurrence5QuotientConstant_coeff_118
  recurrence5QuotientConstant_coeff_119
  recurrence5QuotientConstant_coeff_120
  recurrence5QuotientConstant_coeff_121
  recurrence5QuotientConstant_coeff_122
  recurrence5QuotientConstant_coeff_123
  recurrence5QuotientConstant_coeff_124
  recurrence5QuotientConstant_coeff_125
  recurrence5QuotientConstant_coeff_126
  recurrence5QuotientConstant_coeff_127
  recurrence5QuotientConstant_coeff_128
  recurrence5QuotientConstant_coeff_129
  recurrence5QuotientConstant_coeff_130
  recurrence5QuotientConstant_coeff_131
  recurrence5QuotientConstant_coeff_132
  recurrence5QuotientConstant_coeff_133
  recurrence5QuotientConstant_coeff_134
  recurrence5QuotientConstant_coeff_135
  recurrence5QuotientConstant_coeff_136
  recurrence5QuotientConstant_coeff_137
  recurrence5QuotientConstant_coeff_138
  recurrence5QuotientConstant_coeff_139
  recurrence5QuotientConstant_coeff_140
  recurrence5QuotientConstant_coeff_141
  recurrence5QuotientConstant_coeff_142
  recurrence5QuotientConstant_coeff_143
  recurrence5QuotientConstant_coeff_144
  recurrence5QuotientConstant_coeff_145
  recurrence5QuotientConstant_coeff_146
  recurrence5QuotientConstant_coeff_147
  recurrence5QuotientConstant_coeff_148
  recurrence5QuotientConstant_coeff_149
  recurrence5QuotientConstant_coeff_150
  recurrence5QuotientConstant_coeff_151
  recurrence5QuotientConstant_coeff_152
  recurrence5QuotientConstant_coeff_153
  recurrence5QuotientConstant_coeff_154
  recurrence5QuotientConstant_coeff_155
  recurrence5QuotientConstant_coeff_156
  recurrence5QuotientConstant_coeff_157
  recurrence5QuotientConstant_coeff_158
  recurrence5QuotientConstant_coeff_159
  recurrence5QuotientConstant_coeff_160
  recurrence5QuotientConstant_coeff_161
  recurrence5QuotientConstant_coeff_162
  recurrence5QuotientConstant_coeff_163
  recurrence5QuotientConstant_coeff_164
  recurrence5QuotientConstant_coeff_165

attribute [local simp]
  recurrence5QuotientConstant_coeff_166
  recurrence5QuotientConstant_coeff_167
  recurrence5QuotientConstant_coeff_168
  recurrence5QuotientConstant_coeff_169
  recurrence5QuotientConstant_coeff_170
  recurrence5QuotientConstant_coeff_171
  recurrence5QuotientConstant_coeff_172
  recurrence5QuotientConstant_coeff_173
  recurrence5QuotientConstant_coeff_174
  recurrence5QuotientConstant_coeff_175
  recurrence5QuotientConstant_coeff_176
  recurrence5QuotientConstant_coeff_177
  recurrence5QuotientConstant_coeff_178
  recurrence5QuotientConstant_coeff_179
  recurrence5QuotientConstant_coeff_180
  recurrence5QuotientConstant_coeff_181
  recurrence5QuotientConstant_coeff_182
  recurrence5QuotientConstant_coeff_183
  recurrence5QuotientConstant_coeff_184
  recurrence5QuotientConstant_coeff_185
  recurrence5QuotientConstant_coeff_186
  recurrence5QuotientConstant_coeff_187
  recurrence5QuotientConstant_coeff_188
  recurrence5QuotientConstant_coeff_189
  recurrence5QuotientConstant_coeff_190
  recurrence5QuotientConstant_coeff_191
  recurrence5QuotientConstant_coeff_192
  recurrence5QuotientConstant_coeff_193
  recurrence5QuotientConstant_coeff_194
  recurrence5QuotientConstant_coeff_195
  recurrence5QuotientConstant_coeff_196
  recurrence5QuotientConstant_coeff_197
  recurrence5QuotientConstant_coeff_198
  recurrence5QuotientConstant_coeff_199
  recurrence5QuotientConstant_coeff_200
  recurrence5QuotientConstant_coeff_201
  recurrence5QuotientConstant_coeff_202
  recurrence5QuotientConstant_coeff_203
  recurrence5QuotientConstant_coeff_204
  recurrence5QuotientConstant_coeff_205
  recurrence5QuotientConstant_coeff_206
  recurrence5QuotientConstant_coeff_207
  recurrence5QuotientConstant_coeff_208
  recurrence5QuotientConstant_coeff_209
  recurrence5QuotientConstant_coeff_210
  recurrence5QuotientConstant_coeff_211
  recurrence5QuotientConstant_coeff_212
  recurrence5QuotientConstant_coeff_213
  recurrence5QuotientConstant_coeff_214
  recurrence5QuotientConstant_coeff_215
  recurrence5QuotientConstant_coeff_216
  recurrence5QuotientConstant_coeff_217
  recurrence5QuotientConstant_coeff_218
  recurrence5QuotientConstant_coeff_219
  recurrence5QuotientConstant_coeff_220
  recurrence5QuotientConstant_coeff_221
  recurrence5QuotientConstant_coeff_222
  recurrence5QuotientConstant_coeff_223
  recurrence5QuotientConstant_coeff_224
  recurrence5QuotientConstant_coeff_225
  recurrence5QuotientConstant_coeff_226
  recurrence5QuotientConstant_coeff_227
  recurrence5QuotientConstant_coeff_228
  recurrence5QuotientConstant_coeff_229

attribute [local simp]
  recurrence5QuotientConstant_coeff_230
  recurrence5QuotientConstant_coeff_231
  recurrence5QuotientConstant_coeff_232
  recurrence5QuotientConstant_coeff_233
  recurrence5QuotientConstant_coeff_234
  recurrence5QuotientConstant_coeff_235
  recurrence5QuotientConstant_coeff_236
  recurrence5QuotientConstant_coeff_237
  recurrence5QuotientConstant_coeff_238
  recurrence5QuotientConstant_coeff_239
  recurrence5QuotientConstant_coeff_240
  recurrence5QuotientConstant_coeff_241
  recurrence5QuotientConstant_coeff_242
  recurrence5QuotientConstant_coeff_243
  recurrence5QuotientConstant_coeff_244
  recurrence5QuotientConstant_coeff_245
  recurrence5QuotientConstant_coeff_246
  recurrence5QuotientConstant_coeff_247
  recurrence5QuotientConstant_coeff_248
  recurrence5QuotientConstant_coeff_249
  recurrence5QuotientConstant_coeff_250
  recurrence5QuotientConstant_coeff_251
  recurrence5QuotientConstant_coeff_252
  recurrence5QuotientConstant_coeff_253
  recurrence5QuotientConstant_coeff_254
  recurrence5QuotientConstant_coeff_255
  recurrence5QuotientConstant_coeff_256
  recurrence5QuotientConstant_coeff_257
  recurrence5QuotientConstant_coeff_258
  recurrence5QuotientConstant_coeff_259
  recurrence5QuotientConstant_coeff_260
  recurrence5QuotientConstant_coeff_261
  recurrence5QuotientConstant_coeff_262
  recurrence5QuotientConstant_coeff_263
  recurrence5QuotientConstant_coeff_264
  recurrence5QuotientConstant_coeff_265
  recurrence5QuotientConstant_coeff_266
  recurrence5QuotientConstant_coeff_267
  recurrence5QuotientConstant_coeff_268
  recurrence5QuotientConstant_coeff_269
  recurrence5QuotientConstant_coeff_270
  recurrence5QuotientConstant_coeff_271
  recurrence5QuotientConstant_coeff_272
  recurrence5QuotientConstant_coeff_273
  recurrence5QuotientConstant_coeff_274
  recurrence5QuotientConstant_coeff_275
  recurrence5QuotientConstant_coeff_276
  recurrence5QuotientConstant_coeff_277
  recurrence5QuotientConstant_coeff_278
  recurrence5QuotientConstant_coeff_279
  recurrence5QuotientConstant_coeff_280
  recurrence5QuotientConstant_coeff_281
  recurrence5QuotientConstant_coeff_282
  recurrence5QuotientConstant_coeff_283
  recurrence5QuotientConstant_coeff_284
  recurrence5QuotientConstant_coeff_285
  recurrence5QuotientConstant_coeff_286
  recurrence5QuotientConstant_coeff_287
  recurrence5QuotientConstant_coeff_288
  recurrence5QuotientConstant_coeff_289
  recurrence5QuotientConstant_coeff_290
  recurrence5QuotientConstant_coeff_291
  recurrence5QuotientConstant_coeff_292
  recurrence5QuotientConstant_coeff_293

attribute [local simp]
  recurrence5QuotientConstant_coeff_294
  recurrence5QuotientConstant_coeff_295
  recurrence5QuotientConstant_coeff_296
  recurrence5QuotientConstant_coeff_297
  recurrence5QuotientConstant_coeff_298
  recurrence5QuotientConstant_coeff_299
  recurrence5QuotientConstant_coeff_300
  recurrence5QuotientConstant_coeff_301
  recurrence5QuotientConstant_coeff_302
  recurrence5QuotientConstant_coeff_303
  recurrence5QuotientConstant_coeff_304
  recurrence5QuotientConstant_coeff_305
  recurrence5QuotientConstant_coeff_306
  recurrence5QuotientConstant_coeff_307
  recurrence5QuotientConstant_coeff_308
  recurrence5QuotientConstant_coeff_309
  recurrence5QuotientConstant_coeff_310
  recurrence5QuotientConstant_coeff_311
  recurrence5QuotientConstant_coeff_312
  recurrence5QuotientConstant_coeff_313

private theorem recurrence5Scalar0Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (222 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_222 :
    recurrence5Scalar0Main.coeff 222 =
      -((((((30844441961 * 10 ^ 70 +
        3702612428305070532498259269844984511670061521240956827489598160312699) * 10 ^ 70 +
        4412083180489522337679868854540200853115894733976904793593289512657333) * 10 ^ 70 +
        5830330009493478249618700961352748017943048540811138040613030430195485) * 10 ^ 70 +
        2679016155210242535151535122963634772683601356606702198770863974075000) * 10 ^ 70 +
        5143935265706898155230597189749029861402345315793913250098593092292288) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 0 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 26 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (223 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_223 :
    recurrence5Scalar0Main.coeff 223 =
      ((((((25744311500 * 10 ^ 70 +
        8910056892287104700398464069215547396442995793593877006092702413352796) * 10 ^ 70 +
        4483512835124751095381940844719432433918162499023310227814034180364876) * 10 ^ 70 +
        3499356070603612809841488471133885955970421696201020237289086761689037) * 10 ^ 70 +
        7907123824689660637987285766766429861745960714465038363312507324654086) * 10 ^ 70 +
        1099726638990807209406923121957124162589794533375797769372894077433622) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 0 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 26 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (224 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_224 :
    recurrence5Scalar0Main.coeff 224 =
      -((((((21133887237 * 10 ^ 70 +
        3868118564492008832301375364464639212231361965145042930815592291751606) * 10 ^ 70 +
        0597810545547422735383163479231444747453587257043825139588522249902232) * 10 ^ 70 +
        8183076180631717410303935499085665990729020546267599049413980795860446) * 10 ^ 70 +
        2802799064655125579961689683361048119055588487555971798680006085208851) * 10 ^ 70 +
        6399870756126828693232313933183624946787431480557017458450700903469157) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 0 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 26 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (225 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_225 :
    recurrence5Scalar0Main.coeff 225 =
      ((((((17061295305 * 10 ^ 70 +
        0216439458143337784781464567647225475550111635374108731636690411385728) * 10 ^ 70 +
        5373448233196128441095140768009376747472260209339444944865309676670105) * 10 ^ 70 +
        9822257430782519162516651962857532760724397540623475583877703784172407) * 10 ^ 70 +
        2519608877152993846132450564782610493526491306573984230697294863127301) * 10 ^ 70 +
        3209653569100316909794742451556949759419413379358681081662674029535506) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 0 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 26 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (226 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_226 :
    recurrence5Scalar0Main.coeff 226 =
      -((((((13542962637 * 10 ^ 70 +
        6863477405948706819217582930004556114428514402038859672778164325994255) * 10 ^ 70 +
        7279428632162915658517077579735433654363323789010917773226872440158387) * 10 ^ 70 +
        6493176876764123214665354950312411590415332455552999532935230050373117) * 10 ^ 70 +
        9585154230905816940443786895480416924830470714536506904604485347910772) * 10 ^ 70 +
        8011853544885869420166704799602777990256075189838501402375242294612934) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 0 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 26 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (227 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_227 :
    recurrence5Scalar0Main.coeff 227 =
      ((((((10568500565 * 10 ^ 70 +
        7875467465871162422252881216030880445334826475979417003808979157206427) * 10 ^ 70 +
        1176019494183676663213449002480725276252443971745080420806748948957543) * 10 ^ 70 +
        5510570335681094599570561366270282580530161665018725487626538518521586) * 10 ^ 70 +
        5335026147438170183957816636439110201047083183431171179731961925086898) * 10 ^ 70 +
        4017482334599262353166332476190611319579394518837104940941114170340145) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 0 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 26 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (228 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_228 :
    recurrence5Scalar0Main.coeff 228 =
      -((((((8106536459 * 10 ^ 70 +
        1958893905446750309181881203227386400094251156821386941687046291123596) * 10 ^ 70 +
        5923603619577431074809358839930244639016688063405545994807277555582967) * 10 ^ 70 +
        4916103700215242915940478957015964123889519446007996548073162082122315) * 10 ^ 70 +
        3262847676261827452047053464987805519570526503551919389467827289736991) * 10 ^ 70 +
        7992411577152313644164025362856142632883303714488990494799083734939243) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 0 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 26 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (229 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_229 :
    recurrence5Scalar0Main.coeff 229 =
      ((((((6110832019 * 10 ^ 70 +
        9908572865423678791835537204995868298887489800487037197402001883829415) * 10 ^ 70 +
        8547639465506701382469190420622102695017239930571648054197033874469126) * 10 ^ 70 +
        8295923757549549989383763937794367231603476361801529685036859506749490) * 10 ^ 70 +
        0046719200507837027892350542914592498018520523087966625935617459716110) * 10 ^ 70 +
        1009052162223176033584918445136590719301776689464478838125007790495531) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 0 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 26 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (230 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_230 :
    recurrence5Scalar0Main.coeff 230 =
      -((((((4526130256 * 10 ^ 70 +
        7587224640329205897045989497749103578219851286750625439997049225756264) * 10 ^ 70 +
        9928505291822044704940619845774838148580633647712764296447356930693442) * 10 ^ 70 +
        2047580808949533331499553048399540250194626773065597557656493015477664) * 10 ^ 70 +
        4369249071484652368287752724529980270890523886922214333588973669093944) * 10 ^ 70 +
        0226453555845174428216727637919866310746748841665694866495314383858623) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 0 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 26 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (231 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_231 :
    recurrence5Scalar0Main.coeff 231 =
      ((((((3293314711 * 10 ^ 70 +
        3940497493298293813281216403514673536922063761425228569391744852659454) * 10 ^ 70 +
        9180007024723230090859426009185756433562056704647769143041653758517079) * 10 ^ 70 +
        2884512436175012925395853209349600384876096505952735770532564756985478) * 10 ^ 70 +
        3904416921173106497909113145732832896447543426249813439801198804564592) * 10 ^ 70 +
        3138141178503005557778284990435055520622405995511203497406017935272191) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 0 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 26 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (232 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_232 :
    recurrence5Scalar0Main.coeff 232 =
      -((((((2353619657 * 10 ^ 70 +
        0530507939321283850881764117548582243320128317191319276132408905844221) * 10 ^ 70 +
        2322306144865868540222225419489104699212641254165840350717112084459454) * 10 ^ 70 +
        1304551978652307114211093067015919604033137969068061489568022141935991) * 10 ^ 70 +
        5437454671638196258466650729822243055222537780714806509332034868027285) * 10 ^ 70 +
        2943026307089148773930205502369128899860825919142317660139028735089700) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 0 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 26 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (233 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_233 :
    recurrence5Scalar0Main.coeff 233 =
      ((((((1651777781 * 10 ^ 70 +
        0322414204544410850468094938207520102442137844633136125470013355422636) * 10 ^ 70 +
        6218097276092668062476476788762188914803540884751339553854052861129739) * 10 ^ 70 +
        4475191177619810938538901356528606036274388577136143789585701740773244) * 10 ^ 70 +
        9659085681702007078834385062216309707479321343698063125531537500986987) * 10 ^ 70 +
        2330875023048006599968040116753615758242022852588142027475688402422947) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 0 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 26 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (234 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_234 :
    recurrence5Scalar0Main.coeff 234 =
      -((((((1138116984 * 10 ^ 70 +
        5646224068116430419135235545314943725858964354412545212078557945977621) * 10 ^ 70 +
        9659803686189116414259354004262365971290542067437097136814207093553182) * 10 ^ 70 +
        3572820545732378660159940110376662595516002667723908093453816347107332) * 10 ^ 70 +
        4825193746739671299661179322029680744181481024698077213435257112930340) * 10 ^ 70 +
        4629536178269318888415835882328160411066498625501853392458123128605811) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 0 +
    235 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 26 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (235 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_235 :
    recurrence5Scalar0Main.coeff 235 =
      ((((((769711463 * 10 ^ 70 +
        6542761724474303339304475988160087100213950498558418570727518680870605) * 10 ^ 70 +
        4178586824459689597613337261786696379874248560384933145406899034920044) * 10 ^ 70 +
        8523516336079974995702563906784043524114813439973436590909862075846071) * 10 ^ 70 +
        8119954225854720744023950503422530990345201944864740984240702824114678) * 10 ^ 70 +
        3737991522615172113927686385863282683421914514482566874725379815319874) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 0 +
    236 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 26 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (236 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_236 :
    recurrence5Scalar0Main.coeff 236 =
      -((((((510751345 * 10 ^ 70 +
        8399966419058841420348136829675347722900268815669915582209433995589684) * 10 ^ 70 +
        2051194038949629231539657033657740981864472368783633923355937606504176) * 10 ^ 70 +
        3683332937485811200867039886353035309809057799320175834440011389528801) * 10 ^ 70 +
        9518730381182990399869111731209853974935414934715309245646767239827789) * 10 ^ 70 +
        7544374496596607329671529018371299754480423305709594500578238643766365) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 0 +
    237 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 26 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (237 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_237 :
    recurrence5Scalar0Main.coeff 237 =
      ((((((332321957 * 10 ^ 70 +
        9047959110669757004524790263847346118112885584693192268766581965139896) * 10 ^ 70 +
        8675523632572625842367140050369256552926430120761495102448141381795550) * 10 ^ 70 +
        4245889113527909866475022850403197675467619576316599618155134452622638) * 10 ^ 70 +
        7505711313672709706590400753646501677170775107839799017015909550657194) * 10 ^ 70 +
        0972309438007858171881939957040188455176291409180689356909793794694795) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 0 +
    238 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 26 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (238 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_238 :
    recurrence5Scalar0Main.coeff 238 =
      -((((((211783804 * 10 ^ 70 +
        8761856690013745205941970556557218093658256508366985030787548197709854) * 10 ^ 70 +
        6756381570560257001815426034254079325644797671344316210143678118769862) * 10 ^ 70 +
        8744774244298633740036395456033258056486898566299116987666706068724827) * 10 ^ 70 +
        3429422204633670340314387553372335044281557291214160045445154364931134) * 10 ^ 70 +
        7338126807220827625786089887086300369575241036698269458866129173313710) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 0 +
    239 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 26 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (239 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_239 :
    recurrence5Scalar0Main.coeff 239 =
      ((((((131924857 * 10 ^ 70 +
        5286191418324491544650055066091419056065302898447051365768534195506327) * 10 ^ 70 +
        3796338542071206846545123383329984401878650709916124637308306235075531) * 10 ^ 70 +
        2025310599769279300565311493665749983238885747042145810933133192625586) * 10 ^ 70 +
        9935695993542011620151713916928340793387589522230201368313558156890521) * 10 ^ 70 +
        6138885670044276736185412115283858749225249230297220220366096026842286) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 0 +
    240 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 26 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (240 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_240 :
    recurrence5Scalar0Main.coeff 240 =
      -((((((80025439 * 10 ^ 70 +
        9028985516013163621583423244991144999903127678671125495400205710088747) * 10 ^ 70 +
        1003453180944402245352126671158128080663119654305323672405094461711828) * 10 ^ 70 +
        2930443879573815285773707210835613388067675531329735113152306436253583) * 10 ^ 70 +
        4778581406154531662221227218902699660573282897320264581409969352944102) * 10 ^ 70 +
        5150391119675949808286546346730926201125340912850858861420639335124433) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 0 +
    241 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 26 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (241 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_241 :
    recurrence5Scalar0Main.coeff 241 =
      ((((((46939815 * 10 ^ 70 +
        6971515558350776647671395539772964493330528320491148219146199604921758) * 10 ^ 70 +
        7478804606994365603896560654480536572775229455490407224201299394183467) * 10 ^ 70 +
        4347565416466829191102943122801832563537920131448372854337099759292827) * 10 ^ 70 +
        3642779667602503706400640471052314462809046565294745017198825967884471) * 10 ^ 70 +
        1931750697224870901166711274735254316838319978280989944906614410029483) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 0 +
    242 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 26 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (242 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_242 :
    recurrence5Scalar0Main.coeff 242 =
      -((((((26263010 * 10 ^ 70 +
        7381676958384572370028496925710143058011112283377265640499660557631750) * 10 ^ 70 +
        4545037124476063744333073357782026458096673227365068917342168700104296) * 10 ^ 70 +
        0572756522158939314237026902542002020774183422068726550847843370259751) * 10 ^ 70 +
        5682204444175236065530868947331064746625086251138604492409464658658473) * 10 ^ 70 +
        5779480534765809443114077103641806212410372325862003905778732440532277) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 0 +
    243 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (243 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_243 :
    recurrence5Scalar0Main.coeff 243 =
      ((((((13620277 * 10 ^ 70 +
        9707329198578833525760789416769819209663745648982502493447044284951983) * 10 ^ 70 +
        0264180917765857042987987151317156114775435315742152274739653360914763) * 10 ^ 70 +
        6985005069831976562637579187402059337394030952923244699807195233081122) * 10 ^ 70 +
        5805908799559402351624201631297786614384574864565250050449883736453854) * 10 ^ 70 +
        2850630672332368726792478944440010098481955181162458394994944415035533) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 0 +
    244 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 26 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (244 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_244 :
    recurrence5Scalar0Main.coeff 244 =
      -((((((6092011 * 10 ^ 70 +
        8184072620806129454505185897241693752690697132564100706405001473565397) * 10 ^ 70 +
        3387325213747148170661117585642893753051852573376376572949375976594926) * 10 ^ 70 +
        8681643845621860046277175582980009771818621295761713303750823984655650) * 10 ^ 70 +
        2855302544639266827406475588168938163031695030591727236248884694189935) * 10 ^ 70 +
        8190169821581160115792827216599429747950156452002842597368191440757597) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 0 +
    245 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 26 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (245 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_245 :
    recurrence5Scalar0Main.coeff 245 =
      ((((((1769494 * 10 ^ 70 +
        2995514041539931503190781810112205465657074560177283620124398990090569) * 10 ^ 70 +
        2196874620723535832966070942062002342444884926479956952697512849890444) * 10 ^ 70 +
        7175287922790255567840944829797167557415902573111553782361125523693688) * 10 ^ 70 +
        3284396696220879411394496713021447747879087257107607080362186568119997) * 10 ^ 70 +
        3103716081433698596444766842761900793667513433194090538304887759697814) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 0 +
    246 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 26 +
      92 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (246 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_246 :
    recurrence5Scalar0Main.coeff 246 =
      ((((((573838 * 10 ^ 70 +
        3731126455509939359368264229895426326339587196144879866457001842668015) * 10 ^ 70 +
        8906444468831027961010428719169606542246998786098382547607641229831612) * 10 ^ 70 +
        3206177538858944097695096492704771559172382756475467445491625525812285) * 10 ^ 70 +
        2116753956209984967240025722371702841224368021127618487835809123125081) * 10 ^ 70 +
        3574333259482583797284663800802945852270379738284149725884100186936145) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 0 +
    247 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (247 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_247 :
    recurrence5Scalar0Main.coeff 247 =
      -((((((1716011 * 10 ^ 70 +
        0185272408295949573212240991853889826894750216287009507376247695385209) * 10 ^ 70 +
        8775626718744429505138877414582404044949097160056826193701229788108336) * 10 ^ 70 +
        5865769634458985586374927302439240578347096083468039231750387159903495) * 10 ^ 70 +
        3952696152873103402848297506877640097560573768261368459994637855004575) * 10 ^ 70 +
        2502034317814022041511288458236637405899051435944039852865104010733468) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 0 +
    248 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 26 +
      94 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (248 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_248 :
    recurrence5Scalar0Main.coeff 248 =
      ((((((2146337 * 10 ^ 70 +
        1083285880874506211424847593089460142041429870449762323453563501940402) * 10 ^ 70 +
        2559007125639825945326570871933454979437208698760519427285571478776682) * 10 ^ 70 +
        5534859620836955036630700343595261543724086726559546595798136454490440) * 10 ^ 70 +
        7623490867584250788198687369795857218707686505840285991049592017963268) * 10 ^ 70 +
        7123420033845835687996588201861638515040517654796544589969780020218701) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 0 +
    249 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 26 +
      95 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (249 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_249 :
    recurrence5Scalar0Main.coeff 249 =
      -((((((2171009 * 10 ^ 70 +
        7399613232637162848827089745923294065808071545967411797769591688415208) * 10 ^ 70 +
        5392703280306040360383389902471962738186014203817972083719586591665720) * 10 ^ 70 +
        1736425891118532711157308343455080408153042912986406194455773723497340) * 10 ^ 70 +
        4092464824404825003227662615352294666898913346224282951830776464215791) * 10 ^ 70 +
        2038346013336126982612716896340812316729125587358228693999101293625551) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 0 +
    250 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 26 +
      96 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (250 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_250 :
    recurrence5Scalar0Main.coeff 250 =
      ((((((1980787 * 10 ^ 70 +
        9668305277033666330788785515140625163980194204308420246008299898285444) * 10 ^ 70 +
        8305108354502962958876659749797562398439736771562910734251865415684451) * 10 ^ 70 +
        7306449160170244241861365877397909197632178376395131988654822066889949) * 10 ^ 70 +
        7863688286339559131630096134994721999171035485939483400026765272422234) * 10 ^ 70 +
        4754591585381314196865227535443186101368425691108037503887505690697341) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 0 +
    251 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 26 +
      97 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (251 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_251 :
    recurrence5Scalar0Main.coeff 251 =
      -((((((1693427 * 10 ^ 70 +
        3882830399453670629041245591675802490815520301999694850942027585162909) * 10 ^ 70 +
        2364302444060842631219168302398573189191048735317528141882931502463326) * 10 ^ 70 +
        7937587103447162777393172629125514445941067472666162439877920391080203) * 10 ^ 70 +
        0035715429536617740646350756132702912933871647472397587623164967892175) * 10 ^ 70 +
        1698161538507898280342632859687017783653670618397173249300343986594818) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 0 +
    252 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 252 = 32 +
      220 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 26 +
      98 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (252 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_252 :
    recurrence5Scalar0Main.coeff 252 =
      ((((((1380011 * 10 ^ 70 +
        0797476472533087116303512825731078453772670404738106337369921391800409) * 10 ^ 70 +
        4771263549154173402334239713174671980239272483383936837581894664376908) * 10 ^ 70 +
        7684322483314320244248282305194542182147888002536064279125528848365098) * 10 ^ 70 +
        1745615691763582763358966159797078243819541854896741477464459589193082) * 10 ^ 70 +
        2847170301551573982812916378984371999400802129375189351692566097166844) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 0 +
    253 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 253 = 32 +
      221 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 26 +
      99 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (253 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_253 :
    recurrence5Scalar0Main.coeff 253 =
      -((((((1081397 * 10 ^ 70 +
        6157455929953833892651207625355220450072430043386737146677146937429226) * 10 ^ 70 +
        9733585917843323505724963660211809517028371944992861737682454284398206) * 10 ^ 70 +
        5332743888590717273540703024151360060507319606038674320046529250616909) * 10 ^ 70 +
        2271082220242323727455673519306744915232693674589458422355926101243949) * 10 ^ 70 +
        9827606529736940574176523914761575655160740490525949323872167823030106) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 0 +
    254 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 254 = 32 +
      222 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 26 +
      100 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (254 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_254 :
    recurrence5Scalar0Main.coeff 254 =
      ((((((818751 * 10 ^ 70 +
        3095138178099077009539441864140705665634580504178488616899295914982191) * 10 ^ 70 +
        9344094852806479791034900302195782780595870337415515207205256185539764) * 10 ^ 70 +
        0883444603188215008523846710254488454344306061103745244195016156755147) * 10 ^ 70 +
        4982173111826574041700315604824507680747675613298448039143470749691965) * 10 ^ 70 +
        8064729739312956141737909633497947880423608565706335502644523002857000) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 0 +
    255 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 255 = 32 +
      223 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 26 +
      101 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (255 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_255 :
    recurrence5Scalar0Main.coeff 255 =
      -((((((600534 * 10 ^ 70 +
        4523183783119240014316643126682810769803953107446368270094672329448760) * 10 ^ 70 +
        8164141038164890224002637673068647042460063357059323681068612217020356) * 10 ^ 70 +
        1972747869652914241629766023377171533699337555212642264699590827067770) * 10 ^ 70 +
        5878020750491467941916106362207906707632097509751715205497144822756923) * 10 ^ 70 +
        8617551145270881247677187826937462271456282567332854647715234024277128) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 0 +
    256 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 256 = 32 +
      224 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 26 +
      102 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (256 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_256 :
    recurrence5Scalar0Main.coeff 256 =
      ((((((427313 * 10 ^ 70 +
        9476149369462211045999808808382402124573521097417760998437816869872448) * 10 ^ 70 +
        2670035287099806914061573242237325239853599487934331813875535013646505) * 10 ^ 70 +
        5684367516459738186516701102283538868575783526432864538347669195734690) * 10 ^ 70 +
        0439424601540895933552998388004222347514955948794002840677501651191216) * 10 ^ 70 +
        3869666130706183370297151140937537051327873578892860110145501070332859) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 0 +
    257 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 257 = 32 +
      225 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 26 +
      103 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (257 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_257 :
    recurrence5Scalar0Main.coeff 257 =
      -((((((295124 * 10 ^ 70 +
        5829161899684461035969170229829743955797727682891834442679485431834285) * 10 ^ 70 +
        2064140347545670504997970761001072580029433048388541252579905190934766) * 10 ^ 70 +
        6068789778117251293736967462095592233098303687040371293815327193176614) * 10 ^ 70 +
        3255199909401891739398248398116651870375188299633604700631707824165500) * 10 ^ 70 +
        1540510939020096055952683202325622326554456797473419559965324742520619) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 0 +
    258 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 258 = 32 +
      226 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 26 +
      104 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (258 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_258 :
    recurrence5Scalar0Main.coeff 258 =
      ((((((197802 * 10 ^ 70 +
        0361255320481585155477179667795579932146161125345043051841803428474301) * 10 ^ 70 +
        3391681424893392694299563719230263244653764746863063371735126438212355) * 10 ^ 70 +
        2431055567700123068177160341638034605243078997656270181897273734281151) * 10 ^ 70 +
        7278020469898172624883862732902621718595225033940852697601253540887605) * 10 ^ 70 +
        9548879895922200431834801054459684990420601299850349098102430507973870) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 0 +
    259 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 259 = 32 +
      227 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 26 +
      105 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (259 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_259 :
    recurrence5Scalar0Main.coeff 259 =
      -((((((128538 * 10 ^ 70 +
        9355918160906558534761721099474633210860183957039804536602496069694465) * 10 ^ 70 +
        9946543031892299254358446052296021399656220225478038820900558982439124) * 10 ^ 70 +
        9238136744664319440865304973651646349328665338909979679468039670241685) * 10 ^ 70 +
        1868592604118010294523984816270040944783163895250130224400059196346770) * 10 ^ 70 +
        1925194646426095907339006293308078316330865314189687807804514895429469) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 0 +
    260 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 260 = 32 +
      228 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 26 +
      106 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (260 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_260 :
    recurrence5Scalar0Main.coeff 260 =
      ((((((80846 * 10 ^ 70 +
        7201319151107168976164594126044831093349103925664792810587659014547137) * 10 ^ 70 +
        4670890356649951313678252964641262507414071710435687509408578521354329) * 10 ^ 70 +
        0669801243772668268235072407415930349460114391015163498246898810354384) * 10 ^ 70 +
        7663494394439151324285057191492185227661423477692642516360191022624947) * 10 ^ 70 +
        2710060752395010362425461137052757919129290348976170322351469339274339) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 0 +
    261 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 261 = 32 +
      229 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 26 +
      107 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (261 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_261 :
    recurrence5Scalar0Main.coeff 261 =
      -((((((49074 * 10 ^ 70 +
        1528136335395867058784326906226976676973536655160598141449477290963252) * 10 ^ 70 +
        0933874530728404799324700068729419031962925768985928847709585874437741) * 10 ^ 70 +
        4459133666161894008630286625944631393365990590402790596466592006489979) * 10 ^ 70 +
        8156011348223426241196408349231075976694602443099408268460532712513304) * 10 ^ 70 +
        0535483283170351147631360597469977751613369996682528272329349235335255) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 0 +
    262 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 262 = 32 +
      230 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 26 +
      108 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (262 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_262 :
    recurrence5Scalar0Main.coeff 262 =
      ((((((28612 * 10 ^ 70 +
        9307117225366264999191020947805302340763474240897752817470321026245558) * 10 ^ 70 +
        6313366905546186473412396958175673305457562491824427195838905629095060) * 10 ^ 70 +
        1064913831948331991215321822135954230573521892883306948599986107040813) * 10 ^ 70 +
        5680865709220692210603410432753625373784913698591250712074129191105821) * 10 ^ 70 +
        2024811176061565639032853360936751105926678200311099483247786492759739) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 0 +
    263 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 263 = 32 +
      231 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 26 +
      109 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (263 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_263 :
    recurrence5Scalar0Main.coeff 263 =
      -((((((15900 * 10 ^ 70 +
        4770079540375468176767538140907599610725207551183476848017284566501689) * 10 ^ 70 +
        2527661236932769822495993957066396365619646540312189468498146954307999) * 10 ^ 70 +
        9420318561063592128179123228828391808857385702896283813205508384829876) * 10 ^ 70 +
        2830366633627294904714915527431767315210675377494327035192571541954272) * 10 ^ 70 +
        8618072416398561737161893326609447985672810275889276045063860009460513) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 0 +
    264 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 264 = 32 +
      232 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 26 +
      110 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (264 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_264 :
    recurrence5Scalar0Main.coeff 264 =
      ((((((8307 * 10 ^ 70 +
        3051053690448922250352479480451712232781079360745726943097037661071822) * 10 ^ 70 +
        8156305164281521708223167725038379223222219795713705934417158936355507) * 10 ^ 70 +
        5296883774413074447338279504694039438170393143827681650315726495658941) * 10 ^ 70 +
        3282403708077981571323932112179585307276052441280572104002181396336191) * 10 ^ 70 +
        1022909394762700002925354833548794441810259560109712520889166189557638) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 0 +
    265 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 265 = 32 +
      233 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 26 +
      111 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (265 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_265 :
    recurrence5Scalar0Main.coeff 265 =
      -((((((3972 * 10 ^ 70 +
        9385951616391220827266101687032386529336250394760099883334214071804171) * 10 ^ 70 +
        9614918568337702460894330627325296885336615244758291313319482329436551) * 10 ^ 70 +
        9876389091589066322372933971983811700316578923769336237097484448664141) * 10 ^ 70 +
        1499594111143054017604380359324148468192540297510581602005778459171663) * 10 ^ 70 +
        7429223902215512488952898666809473388702260093385264143558428897420167) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 0 +
    266 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 266 = 32 +
      234 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (266 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_266 :
    recurrence5Scalar0Main.coeff 266 =
      ((((((1632 * 10 ^ 70 +
        8044360520385156492819533684713071585505083177429821800068243736212221) * 10 ^ 70 +
        4655569931069452327106677421733372508189612861923226955326542229246806) * 10 ^ 70 +
        6399058660739740683797152443336261376116429045113268181768472933829179) * 10 ^ 70 +
        0064670692076492491637240002592698581114681389744217519841114047183923) * 10 ^ 70 +
        8298367787405641388624802558408867204326134250871770677077750831753499) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 0 +
    267 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 267 = 32 +
      235 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 26 +
      113 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (267 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_267 :
    recurrence5Scalar0Main.coeff 267 =
      -((((((460 * 10 ^ 70 +
        7126935313106716358980151236850882944391326530099868603256913445419256) * 10 ^ 70 +
        8054649558788778900675086718640344962951503878427554194016671911297257) * 10 ^ 70 +
        4724212657099284559707524246914841849100640654671350280369152720393177) * 10 ^ 70 +
        8021531767286897782961099647481978268688387625585115861750329105316248) * 10 ^ 70 +
        9869910676356028970829152400515779506044155539816039380565904700980700) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 0 +
    268 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 268 = 32 +
      236 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 26 +
      114 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (268 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_268 :
    recurrence5Scalar0Main.coeff 268 =
      -((((((61 * 10 ^ 70 +
        6756874132105653740023577857104787021811662281874906309355442407925385) * 10 ^ 70 +
        6679639617247237405522963376044171808048913343430889569198124356432903) * 10 ^ 70 +
        7228691551347897139044354820687527104489055750127537752553667602773300) * 10 ^ 70 +
        3900578755892806416848614106088951577612959055743045157768133413405850) * 10 ^ 70 +
        9656503797941723527528916324063136317186774813294451323851819180366662) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 0 +
    269 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 269 = 32 +
      237 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 26 +
      115 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (269 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_269 :
    recurrence5Scalar0Main.coeff 269 =
      ((((((245 * 10 ^ 70 +
        7477565733795403577310439843612001076271895374566254321855299566870832) * 10 ^ 70 +
        3394043237493034884546889916688424161341634882154713443568694471451942) * 10 ^ 70 +
        0228879152898430117279493252713507367787984024797352597185428729730167) * 10 ^ 70 +
        9784682566942399251114745415172442313805655842621746474629792607185241) * 10 ^ 70 +
        8476458091437445952492280475259068495843554136648744201075772787135333) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 0 +
    270 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 26 +
      116 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (270 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_270 :
    recurrence5Scalar0Main.coeff 270 =
      -((((((269 * 10 ^ 70 +
        6027407931142175972462885815365867003186710502486437324013106741967780) * 10 ^ 70 +
        6491164420193011522666285330182656388384386008254014410771181425659562) * 10 ^ 70 +
        5895678595171830245190705858546567412119593016867592897958219954675541) * 10 ^ 70 +
        0975502611077369900464876599807119708393228668779970449286585083488881) * 10 ^ 70 +
        6396251512226812039112296060943549666833391248855100147844203429480899) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 0 +
    271 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 26 +
      117 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (271 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_271 :
    recurrence5Scalar0Main.coeff 271 =
      ((((((229 * 10 ^ 70 +
        1964810018942224775427194228492335235959122637205172648080370987148616) * 10 ^ 70 +
        3155273033157861069258938139258614691299883469875395371268974412898734) * 10 ^ 70 +
        3531249655990184202058555475845813218579264413862096046239039691921951) * 10 ^ 70 +
        3649964796392411322941027876958358162038194817716468709660735193545815) * 10 ^ 70 +
        2556788846490664644451729596172033117842102822418618951206850192182241) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 0 +
    272 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 26 +
      118 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (272 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_272 :
    recurrence5Scalar0Main.coeff 272 =
      -((((((172 * 10 ^ 70 +
        2263880250435741652004567120997521976692466184179642823037568603695642) * 10 ^ 70 +
        3472696345208225407501108910135229034104911158588282617501718023360867) * 10 ^ 70 +
        0855494801603576409449882691767076136920536310809245062100580795180380) * 10 ^ 70 +
        5543162552238141411131791928937619522122536012554397908420509439411943) * 10 ^ 70 +
        6078551974156690396279745042953655670402432802713142670153847588110664) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 0 +
    273 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 26 +
      119 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (273 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_273 :
    recurrence5Scalar0Main.coeff 273 =
      ((((((119 * 10 ^ 70 +
        5723298956494730473115697332787019770142434604083286831602641948858229) * 10 ^ 70 +
        9274800889414955463245307608201441467459125732595622373492823550349102) * 10 ^ 70 +
        4398753349358735923316898348212622550930599972324851189930810240186562) * 10 ^ 70 +
        7798782139842652176510921649563478322420636204825021719925643560790125) * 10 ^ 70 +
        1450885642573711376169486462624223477582030670662432078540983738100587) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 0 +
    274 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 26 +
      120 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (274 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_274 :
    recurrence5Scalar0Main.coeff 274 =
      -((((((78 * 10 ^ 70 +
        2302829033987459360570860043025359226412334984795436625926528334694767) * 10 ^ 70 +
        4435967174002547873859890361097717281363020744876005680227785549370633) * 10 ^ 70 +
        6326413253084521689047774963697331722770381474755078739768079872043167) * 10 ^ 70 +
        8055930387007324548326131121987327008655248047218452610507784250195427) * 10 ^ 70 +
        6464055942198348177522440491603763503173510710648940027909516373075347) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 0 +
    275 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (275 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_275 :
    recurrence5Scalar0Main.coeff 275 =
      ((((((48 * 10 ^ 70 +
        7108649227270711521588358663576650698917544392495351782439797964298653) * 10 ^ 70 +
        9790307823825470835082310126562408754204643579270871862624764966619000) * 10 ^ 70 +
        4374899523391098343775685519907438215516872953390513619746260731759349) * 10 ^ 70 +
        0423810168189027603332397157414076821015773246996429593679832002621069) * 10 ^ 70 +
        7628301859778328434054415571387715086865913801378275666478988362925558) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 0 +
    276 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 26 +
      122 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (276 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_276 :
    recurrence5Scalar0Main.coeff 276 =
      -((((((29 * 10 ^ 70 +
        0086550416041781875427525838614998702558918716716740277162709315170247) * 10 ^ 70 +
        5450090986780130445535185113951563649173141735867858589015091380244489) * 10 ^ 70 +
        4992113992564263810338268399664507282193992377203080715302846048091823) * 10 ^ 70 +
        0715755171382580638401789568190762882622375414206957593388055106062362) * 10 ^ 70 +
        9493128787938491429104457429678977123362377285435607141766899537949080) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 0 +
    277 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 277 = 32 +
      245 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 26 +
      123 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (277 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_277 :
    recurrence5Scalar0Main.coeff 277 =
      ((((((16 * 10 ^ 70 +
        5544285574453486580624324811220503078905477077797645625353549824446121) * 10 ^ 70 +
        8997284574266397952216227056973981483945575421640824296582050087757784) * 10 ^ 70 +
        7580047666755275624303411809991571712166059670750454785718993493398396) * 10 ^ 70 +
        7881409434650086558455322492472837382765507603850357348417688862116467) * 10 ^ 70 +
        1640319987202709539589434928733230704498577543965315292759416778290325) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 0 +
    278 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 26 +
      124 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (278 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_278 :
    recurrence5Scalar0Main.coeff 278 =
      -((((((9 * 10 ^ 70 +
        0496194643395963446624896801218653587260813742184843506477059406213158) * 10 ^ 70 +
        0948878317757023275122320662208705209852931883511022298232846478389146) * 10 ^ 70 +
        7467998464722104858792052415391951189775570357807895907227509388656156) * 10 ^ 70 +
        2084041940015776918708054539403329940434090126341316028069860071432435) * 10 ^ 70 +
        1548175226290783935510639402488852347487617543823849921011249625984400) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 0 +
    279 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 26 +
      125 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (279 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_279 :
    recurrence5Scalar0Main.coeff 279 =
      ((((((4 * 10 ^ 70 +
        7267435187749159138574300809600002093146355595969510846947703317849231) * 10 ^ 70 +
        1143473086588687435880483477059399396565195698786436436351752424068533) * 10 ^ 70 +
        7280408925445892707092959272791469507025927738854882298928706570677569) * 10 ^ 70 +
        8945588512976386349744552388105330440727840544710466623616710391681966) * 10 ^ 70 +
        5432574338105396457974646746935469287284872804144445534467079380903439) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 0 +
    280 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 280 = 32 +
      248 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 26 +
      126 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (280 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_280 :
    recurrence5Scalar0Main.coeff 280 =
      -((((((2 * 10 ^ 70 +
        3463803419202550451603366995295714546121779264501535193654798723529163) * 10 ^ 70 +
        7094486486816428850081490521295276889951066587134842773910875097826888) * 10 ^ 70 +
        8567911248318492576762341751244654384392233991973511746741972745283139) * 10 ^ 70 +
        5020870343545453534669838749043428812796458830075133071395067476429557) * 10 ^ 70 +
        6337422489142941339106884148831877502288871099619835910692882067059815) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 0 +
    281 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 281 = 32 +
      249 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 26 +
      127 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (281 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_281 :
    recurrence5Scalar0Main.coeff 281 =
      ((((((1 * 10 ^ 70 +
        0963861535653903230983560131900275888313117952512942143654406466154054) * 10 ^ 70 +
        8494093669128459607282629667210161072623177188098954667391740277847119) * 10 ^ 70 +
        1767766047591584501520577927838604728567039715762346867106122843516329) * 10 ^ 70 +
        0517402207298240565359694857201031906022642682436888631585747844612652) * 10 ^ 70 +
        2122147434264546764688681885482981029077532946244664662352902998944660) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 0 +
    282 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 26 +
      128 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (282 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_282 :
    recurrence5Scalar0Main.coeff 282 =
      -(((((4737597779029215201322073780935997913024179403401648185825613541791478 * 10 ^ 70 +
        8888157209511698696076208222185979533697022554097923730794238324859088) * 10 ^ 70 +
        7858820375774256232148157383090560200632868530033387996168069045886639) * 10 ^ 70 +
        5958762179155648345481691849462327687891837991289747733804600495047151) * 10 ^ 70 +
        4685819733180996552716526583017522272815889230616930784231617775187815) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 0 +
    283 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 26 +
      129 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (283 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_283 :
    recurrence5Scalar0Main.coeff 283 =
      (((((1825140464331015244853409340542735946853836793082509473109345033105912 * 10 ^ 70 +
        4421173293794244099975264846989998204465973368018881669806344173572221) * 10 ^ 70 +
        5426430809337367881752864287364892997263685915521156799576993513651623) * 10 ^ 70 +
        4758876908130582544584268605819821338756293408456357206810151385961671) * 10 ^ 70 +
        5863069087714541095603253740949232983013205747325085122892676694804637) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 0 +
    284 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 284 = 32 +
      252 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 252 = 32 +
      220 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 26 +
      130 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (284 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_284 :
    recurrence5Scalar0Main.coeff 284 =
      -(((((569536826303783270508624081183826167218826629253268114553996796478498 * 10 ^ 70 +
        0446258627315235755347315476611858232938694247508921208512635707537875) * 10 ^ 70 +
        2111335190066987425201177833295720121329666287654561234236197159709980) * 10 ^ 70 +
        8211824216175974540122232143931983819390417521557865234091523805331724) * 10 ^ 70 +
        6515366641922909681672515090838099877996107648010397761125193245685853) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 0 +
    285 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 285 = 32 +
      253 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 253 = 32 +
      221 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 26 +
      131 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (285 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_285 :
    recurrence5Scalar0Main.coeff 285 =
      (((((89990707080948882553345035846080448900093927469479676308112909909811 * 10 ^ 70 +
        2710339817321308474100433919480913308769582017391931323034484802178660) * 10 ^ 70 +
        0077423522502194171633491633273110908983320827801373609426889235629352) * 10 ^ 70 +
        5422893918896652812647087651971364610585670027621306694859115956402781) * 10 ^ 70 +
        0285856321926039832776617652040943822259357971901449249119390233447902) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 0 +
    286 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 286 = 32 +
      254 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 254 = 32 +
      222 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 26 +
      132 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (286 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_286 :
    recurrence5Scalar0Main.coeff 286 =
      (((((55707910454390753668698546935861140829715400402990366110699869356584 * 10 ^ 70 +
        1972821432155164257485294981537296213651068955441428041157756449578690) * 10 ^ 70 +
        1287635212441606601108225286551074165271370101461765483274007988325377) * 10 ^ 70 +
        6258409154980646276785732743076719991387939112410185839502858296833582) * 10 ^ 70 +
        0923838412030397895023325914510732767282787452830758704966878736502573) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 0 +
    287 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 287 = 32 +
      255 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 255 = 32 +
      223 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 26 +
      133 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (287 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_287 :
    recurrence5Scalar0Main.coeff 287 =
      -(((((75014668851914604486204955666923920752200483350261827054514106358400 * 10 ^ 70 +
        5917118870777429198834754701710809661853619172623344553684016589083420) * 10 ^ 70 +
        9909959475623304792449011536782227242725453078246609756787723179128043) * 10 ^ 70 +
        4341741857400762913694787521751281857543966088315756809326498087404444) * 10 ^ 70 +
        9648155243542852852356853917052669813967589513847854279100107061470671) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 0 +
    288 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 288 = 32 +
      256 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 256 = 32 +
      224 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 26 +
      134 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (288 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_288 :
    recurrence5Scalar0Main.coeff 288 =
      (((((56992834019100253562415625480763545393818801915138515427579610547896 * 10 ^ 70 +
        3453865686543063388988329165793989403005882094095369368643474120035614) * 10 ^ 70 +
        5679326180032582039357852994381819535999407132713943156515271919926152) * 10 ^ 70 +
        6505579238261538425740051606407871018275985219943687886283442113894308) * 10 ^ 70 +
        3121281556113892764442421709247529582641218597652148846844675386496565) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 0 +
    289 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 289 = 32 +
      257 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 257 = 32 +
      225 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 26 +
      135 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (289 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_289 :
    recurrence5Scalar0Main.coeff 289 =
      -(((((35062562643548707171903424668329096992473633105625976826767466852343 * 10 ^ 70 +
        8229864756960194348135993483517097885989347279999352467598322314403015) * 10 ^ 70 +
        0311614376923168155218799605668237052735706552407744564979347944749004) * 10 ^ 70 +
        3166351730990793153584987447279556552131546261123354299418308378061462) * 10 ^ 70 +
        2106938616238795224491118990871719945736972250898625789567827286068036) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 0 +
    290 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 290 = 32 +
      258 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 258 = 32 +
      226 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 26 +
      136 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (290 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_290 :
    recurrence5Scalar0Main.coeff 290 =
      (((((18801507739850594243269211671956231439351994567531943415351837793107 * 10 ^ 70 +
        0362928141849985056706518282923011977883549605710010423543999072703371) * 10 ^ 70 +
        3525234029549178989176857196536518199496062241672945957412694076168156) * 10 ^ 70 +
        2105090198705105736745588795070111749851121160573125215365856881936871) * 10 ^ 70 +
        0040125071055323646860081890589696609922340679780571973315877366465713) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 0 +
    291 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 291 = 32 +
      259 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 259 = 32 +
      227 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 26 +
      137 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (291 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_291 :
    recurrence5Scalar0Main.coeff 291 =
      -(((((8921251648103743896680772193259770655451841215482123250994890827976 * 10 ^ 70 +
        7179046592216100567705929752076183556552012516916446906996054014280824) * 10 ^ 70 +
        5220181611780692585897961550920421545451486704331338804732335833010770) * 10 ^ 70 +
        2834138751867177706159495190044842474980364974889769337664220008136117) * 10 ^ 70 +
        7508087984734847586186475522963610464923583922461288680771269775897382) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 0 +
    292 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 292 = 32 +
      260 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 260 = 32 +
      228 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 26 +
      138 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (292 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_292 :
    recurrence5Scalar0Main.coeff 292 =
      (((((3672729505742636739505295398179777726343079001375336766557911490951 * 10 ^ 70 +
        7640492160769124513862845601240282038212373394739971141061901979664825) * 10 ^ 70 +
        9413984167666376638953354594345944603697276153192683051618790772488806) * 10 ^ 70 +
        3065233927143103638760085209200417248826370908759648096518759598043883) * 10 ^ 70 +
        1828493296380177482367661842289694207283320939705560253344110884126523) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 0 +
    293 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 293 = 32 +
      261 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 261 = 32 +
      229 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 26 +
      139 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (293 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_293 :
    recurrence5Scalar0Main.coeff 293 =
      -(((((1206178411702890396451302105176650671256939325284479652226020273855 * 10 ^ 70 +
        5064899250137333030391276853801057012382102433129519819857014795831833) * 10 ^ 70 +
        7721080207265301416910339130179213835509582121140330973528576714791815) * 10 ^ 70 +
        3194931020176520865102487795808073907658030537550251047150557527010768) * 10 ^ 70 +
        8537198257712246760601928600233291964132776806580719379706579050389105) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 0 +
    294 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 294 = 32 +
      262 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 262 = 32 +
      230 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (294 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_294 :
    recurrence5Scalar0Main.coeff 294 =
      (((((203990809213272784676306152549940796314899498639038124315460702185 * 10 ^ 70 +
        7933341044433540593028839163542742304753084800221879014278902650908119) * 10 ^ 70 +
        7898483250659166193989864536177039797536775980750938214615113090001483) * 10 ^ 70 +
        0967372245188077526155380183014697802104654001684152867280688397289202) * 10 ^ 70 +
        1518876823473305877242490725552108224444771442188738018347488467526536) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 0 +
    295 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 295 = 32 +
      263 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 263 = 32 +
      231 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 26 +
      141 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (295 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_295 :
    recurrence5Scalar0Main.coeff 295 =
      (((((116687575366922381177968997408231378651853471570960897460304695482 * 10 ^ 70 +
        9793665062699425805676185059570334616009499954222047607858955048561868) * 10 ^ 70 +
        8498589309210519501692815864575581123329377690428074944125880281332652) * 10 ^ 70 +
        5435041096181529722282974671396091364379612110355058354431859742885285) * 10 ^ 70 +
        2794930318803827625675685187941366315763947115745787813933402608058223) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 0 +
    296 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 296 = 32 +
      264 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 264 = 32 +
      232 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 26 +
      142 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (296 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_296 :
    recurrence5Scalar0Main.coeff 296 =
      -(((((164230467354227233663690465417076818299317792093773730964970728664 * 10 ^ 70 +
        9259205545973335713737466967198714702270121511308478772784032881200315) * 10 ^ 70 +
        7587000816419092458527154065506561821554254831898642324979421227038574) * 10 ^ 70 +
        6975663192848233498999778878691999393034094956216125525109160524869775) * 10 ^ 70 +
        5883766322149807011940255719328540540634072592121251918149439309143502) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 0 +
    297 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 297 = 32 +
      265 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 265 = 32 +
      233 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 26 +
      143 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (297 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_297 :
    recurrence5Scalar0Main.coeff 297 =
      (((((126809263651853093111866578830479574082659726750462603321404429552 * 10 ^ 70 +
        0373516408953452727532450642817409172824315878202230832417105432997898) * 10 ^ 70 +
        0781768278686326681770321642120874700244020278375453248392355753503400) * 10 ^ 70 +
        4561387161727527245204599689197340578409636544308443567099969241037825) * 10 ^ 70 +
        5428814352506031149775175752760540932655536844809699388206710064535511) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 0 +
    298 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 298 = 32 +
      266 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 266 = 32 +
      234 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 26 +
      144 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (298 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_298 :
    recurrence5Scalar0Main.coeff 298 =
      -(((((78758756518799382987099851035580255487325700752489277634497068000 * 10 ^ 70 +
        4882052176945507292425723654227783232588691838916800785660762285054148) * 10 ^ 70 +
        9767970265794768023071686644212068896485020864395829891675602706195001) * 10 ^ 70 +
        4715360165980580258228869406596802303107089035548585817403644502494322) * 10 ^ 70 +
        0438968025866192726167806265275699103407660608413731164622608272880540) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 0 +
    299 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 299 = 32 +
      267 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 267 = 32 +
      235 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 26 +
      145 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (299 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_299 :
    recurrence5Scalar0Main.coeff 299 =
      (((((42496926659035490083462311231549173080222808497441153397262659011 * 10 ^ 70 +
        1754677736643381519385555548926412315862577526449521191966821076711833) * 10 ^ 70 +
        4764519137488631928637620804636849706334265873199067282710544101502827) * 10 ^ 70 +
        6555102962597025417955244355590291947854900674357674567890437166999749) * 10 ^ 70 +
        4114367136037587810487234498588676850233747654966497373094220689650869) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 0 +
    300 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 300 = 32 +
      268 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 268 = 32 +
      236 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 26 +
      146 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (300 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_300 :
    recurrence5Scalar0Main.coeff 300 =
      -(((((20244561275431981180325479877415427698791329631182489975563066092 * 10 ^ 70 +
        2598968134969721757959237094674553543589106187392211147428154143013991) * 10 ^ 70 +
        5988827244595852436998135650850377691244951908107115469793712700917195) * 10 ^ 70 +
        1837917509456883934477226784268324283437250038247625176876305596669494) * 10 ^ 70 +
        9803907466197283374312044416838877461327939224462840781092122262141172) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 0 +
    301 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 301 = 32 +
      269 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 269 = 32 +
      237 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 26 +
      147 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (301 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_301 :
    recurrence5Scalar0Main.coeff 301 =
      (((((8337107661062482681886812827605113713963594944306598899793129302 * 10 ^ 70 +
        6006850748602552086417678819253764503116974160534626254608821126052108) * 10 ^ 70 +
        8980843762916228643994345001995728622994566689221262557713477197764822) * 10 ^ 70 +
        1929344922837683477317303642347495488871194328649226204059314613990785) * 10 ^ 70 +
        2914343445343154846970067855433356514288229564843508496804683813828435) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 0 +
    302 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 302 = 32 +
      270 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 26 +
      148 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (302 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_302 :
    recurrence5Scalar0Main.coeff 302 =
      -(((((2701851446698911515860642379184144373542076635534107805320377020 * 10 ^ 70 +
        2555059858615045670598366864697095775846025799044405961157259531829038) * 10 ^ 70 +
        9151009530897461202958170328221935650316680409882073303055202448123462) * 10 ^ 70 +
        2543845769576381392874378562367782799478338177893220696652220331913642) * 10 ^ 70 +
        0043357925803250349181901326074469693572638152757697580613887943380036) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 0 +
    303 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 303 = 32 +
      271 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 26 +
      149 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (303 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_303 :
    recurrence5Scalar0Main.coeff 303 =
      (((((393552084132156885361956457346128213744747668437903457501102703 * 10 ^ 70 +
        4812536387244080050800217085132647753988378858112120703788271423687527) * 10 ^ 70 +
        9044419195554514272816254084198841065383086607174010809611001093632893) * 10 ^ 70 +
        7699059921330929947876287288382524402156110329007907553487746901520403) * 10 ^ 70 +
        9448529796602397102221115645883468131823857147033584495512173240773098) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 0 +
    304 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 304 = 32 +
      272 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 26 +
      150 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (304 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_304 :
    recurrence5Scalar0Main.coeff 304 =
      (((((351932430421155317097861839515093806041473121312581556921575221 * 10 ^ 70 +
        5913261380806023903075344406273833763102179453179613673639604826021287) * 10 ^ 70 +
        5519081908172359997836868347600615614215805003587474271603823604884591) * 10 ^ 70 +
        5005446338630293972019500019863855268993893115289332986160903040047197) * 10 ^ 70 +
        0669221865020596086194687638757273040810348076875001169918298036261900) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 0 +
    305 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 305 = 32 +
      273 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 26 +
      151 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (305 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_305 :
    recurrence5Scalar0Main.coeff 305 =
      -(((((461715946294240173218245680209883093667474544499330610697754390 * 10 ^ 70 +
        1315752422554987707432488110224309346933783918760679118741736646871388) * 10 ^ 70 +
        0470927504817628686961403887160476284493361381019073847208684359488227) * 10 ^ 70 +
        7205794709024103734160274420514660470956783432635341211225344122175947) * 10 ^ 70 +
        2769813371135039597594924803907924283583940721730340234909639004053678) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 0 +
    306 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 306 = 32 +
      274 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 26 +
      152 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (306 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_306 :
    recurrence5Scalar0Main.coeff 306 =
      (((((367692925162621501381200375884087282320984929660405137487266573 * 10 ^ 70 +
        5684572901770952153731195650390750183063729578941477393232833847420648) * 10 ^ 70 +
        8162692570636651407982954183118041490362626210264621924402529980256166) * 10 ^ 70 +
        5529795880718490709928069967929614173917556756150512909363405198411830) * 10 ^ 70 +
        9398883047860296493612759241261375684160111748720413587484407127510884) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 0 +
    307 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 307 = 32 +
      275 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 26 +
      153 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (307 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_307 :
    recurrence5Scalar0Main.coeff 307 =
      -(((((244041096166669136464102182934472619309933290891979974328729471 * 10 ^ 70 +
        4705580190071922752303075059151761681836801663595685746825948141258423) * 10 ^ 70 +
        4575315085813890932044998020142974627078028829203858960763000190186134) * 10 ^ 70 +
        2077104981993502769159313215636842426428751659531541895268293022305126) * 10 ^ 70 +
        3233919352135509619281918871044387467718575089584512327110980639118338) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 0 +
    308 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 308 = 32 +
      276 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 26 +
      154 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (308 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_308 :
    recurrence5Scalar0Main.coeff 308 =
      (((((145983855230569381328687423787361378781562525451954163261099206 * 10 ^ 70 +
        9097382871079301897452953098165351455156504643554239166334559243421925) * 10 ^ 70 +
        3285482575619788920619805331835456014598566008253925086590791756413320) * 10 ^ 70 +
        0775747140818000189958854496183523955002971292700588200636349214625553) * 10 ^ 70 +
        8715286463057653160059339771895882732180349061131165310237812426686880) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 0 +
    309 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 309 = 32 +
      277 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 277 = 32 +
      245 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 26 +
      155 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (309 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_309 :
    recurrence5Scalar0Main.coeff 309 =
      -(((((81259703745130493940454054574560684665646900898662974927063324 * 10 ^ 70 +
        0870859521416995497741646412453709378719647746932382294105079376766124) * 10 ^ 70 +
        6882385162809149440983639533513522896850041192021773407565943992369553) * 10 ^ 70 +
        4747634530330831020094372525749200255625490996375317002724372031270049) * 10 ^ 70 +
        1650990058749412653708030369918034273126107735690379523728372782903009) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 0 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 26 +
      156 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (310 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_310 :
    recurrence5Scalar0Main.coeff 310 =
      (((((42776768836096540223148740104671486454616604004025234832193370 * 10 ^ 70 +
        3408594748366262933888521672149914671709804006650139847308028815510734) * 10 ^ 70 +
        3461862734302270033295448931303540970660289960169694588937304790488384) * 10 ^ 70 +
        8871202905099678404667676768562319782866834477557773598184321588602974) * 10 ^ 70 +
        1773041873019723796614680057008599998735272082799932551840512387687820) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 0 +
    311 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 26 +
      157 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (311 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_311 :
    recurrence5Scalar0Main.coeff 311 =
      -(((((21493452608151708840139033022044295242428005336424327179229383 * 10 ^ 70 +
        9307615389969318572773909126304979428910865753050986521343451374870965) * 10 ^ 70 +
        7269531999434099932200950892053803127906799695378490842863289469050122) * 10 ^ 70 +
        3211004838094545560454392649918001435470995647569360978224976489098709) * 10 ^ 70 +
        1257579317202069062999604674536610814582988857690979945805735718992370) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 0 +
    312 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 312 = 32 +
      280 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 280 = 32 +
      248 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 26 +
      158 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (312 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_312 :
    recurrence5Scalar0Main.coeff 312 =
      (((((10364633855070496691113392150846515771219881337977145357299741 * 10 ^ 70 +
        2948570806429517729116237710041679886197161769485749655961288163961112) * 10 ^ 70 +
        2680055847673812161146437228557439154599080521680341296317983905732272) * 10 ^ 70 +
        2826036762181821448222615976011363156535947932121096244261732693381799) * 10 ^ 70 +
        1748117227861750583704570886055093791810196912825102904162152339685154) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 0 +
    313 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 313 = 32 +
      281 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 281 = 32 +
      249 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 26 +
      159 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (313 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_313 :
    recurrence5Scalar0Main.coeff 313 =
      -(((((4811806701061781899662313539299400681881885333328625632683833 * 10 ^ 70 +
        6972815340581109519805237755986281794690750510395810880614932714490717) * 10 ^ 70 +
        8046175094241859152355120640413701946629854846262225364007030443102966) * 10 ^ 70 +
        4161547904408670526575469940311464249185537048564993483159220873604424) * 10 ^ 70 +
        3465709675562800112397715670784898071358498149779789042804407220260492) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 0 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 26 +
      160 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (314 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_314 :
    recurrence5Scalar0Main.coeff 314 =
      (((((2153437456443736930285733806939079909860687703395123590730612 * 10 ^ 70 +
        1589210559260373848242491045859897610290730270445547683420365536934471) * 10 ^ 70 +
        2669620167046337355341892022593267718375672866245144640521066474414900) * 10 ^ 70 +
        7533846760143487588825112893450769419321170361604876242019896194523797) * 10 ^ 70 +
        3368239405705056554602861129464259438486793997464121076656148267466180) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 1 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 25 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (315 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_315 :
    recurrence5Scalar0Main.coeff 315 =
      -(((((928582864853115210159674757155774421584676714410465498418913 * 10 ^ 70 +
        0564332297123049702515893863190817988263213512534207593254950670200259) * 10 ^ 70 +
        0365515843089006215074625442234593503680473114172058985913365633304518) * 10 ^ 70 +
        5707968434807116435612663520619645856878195078039177267399268184180148) * 10 ^ 70 +
        6031578091374684383281719027715197139311816865331020260504273517514856) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 2 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 24 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (316 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_316 :
    recurrence5Scalar0Main.coeff 316 =
      (((((384797867696057151076035612091858133195874323077600596344069 * 10 ^ 70 +
        7520025811849449612915273427221242187571822927221723528476018928074623) * 10 ^ 70 +
        7742996577489683987521833785058075409741315968218869906114950800747961) * 10 ^ 70 +
        3657933534456543227140447448078609325675657454628476253620057219802789) * 10 ^ 70 +
        5125310752430377929284212450251075582602433544974640781920194057189144) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 3 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 23 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (317 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_317 :
    recurrence5Scalar0Main.coeff 317 =
      -(((((152350468213636843511231182331566068113014119419452860836469 * 10 ^ 70 +
        5866147524110481322337694781264247553282800371847930821706669146871441) * 10 ^ 70 +
        0186041698851551862060070166722009830376518497379343684028323716221424) * 10 ^ 70 +
        0356459173502443091639666122841471300979062418317106679782314587840391) * 10 ^ 70 +
        9464022449405855794695211716855954083352498183767287008980784091912185) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 4 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 22 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (318 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_318 :
    recurrence5Scalar0Main.coeff 318 =
      (((((56977259457970865552892837852708793831729513110524423701342 * 10 ^ 70 +
        0591812891880041751534105551901418575141366197349252198096738466597667) * 10 ^ 70 +
        9281179256045394829088064124615261529230067038311301344225410812948426) * 10 ^ 70 +
        5169589834166679997453037305635954416838852906656170727202167111344453) * 10 ^ 70 +
        0661987448230725271917621519137943847229682031017250280377920435484750) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 5 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 21 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (319 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_319 :
    recurrence5Scalar0Main.coeff 319 =
      -(((((19668453122037812714546617447269658197878225824797970435907 * 10 ^ 70 +
        6639463451897055200077367170062776314421422590751334102321362320241698) * 10 ^ 70 +
        8489489239508177349078112039629593346188358912631810148511362403277422) * 10 ^ 70 +
        7225579693327186710941977093447290203927363869798756830399198869442347) * 10 ^ 70 +
        9603406601997393233598738511520028540540779810210537046090839581151787) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 6 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 20 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (320 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_320 :
    recurrence5Scalar0Main.coeff 320 =
      (((((5937006318297357578453869663502148560690131498262824720549 * 10 ^ 70 +
        2102409177750205524254228291557863697690062136453115268594154179184976) * 10 ^ 70 +
        1939600943867172313265032218408967274589053629570381796555523401183286) * 10 ^ 70 +
        4254583368726688845257416496670596078288951452284787965738133008794720) * 10 ^ 70 +
        1474011050192607889620533184827419141083646313364961929208254713347610) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 7 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 19 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (321 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_321 :
    recurrence5Scalar0Main.coeff 321 =
      -(((((1311352307905924916786306195773026528063988173936148581660 * 10 ^ 70 +
        1063973040237676458313022998459882304095286360546820103655083859749534) * 10 ^ 70 +
        1986349481471412925286404997328958094644750580840156691022311935632933) * 10 ^ 70 +
        1928878370901690122800158178610615964620198631318251876200566084857359) * 10 ^ 70 +
        0514489083921046411050883430741192457282901395321866406773759995897574) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 8 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 18 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (322 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_322 :
    recurrence5Scalar0Main.coeff 322 =
      -(((((21029889313775075506548710040655110081409655825394927163 * 10 ^ 70 +
        4994632559242933706296553599240330918273282589915138821967723146416806) * 10 ^ 70 +
        2598521321275669169273236162338820510314516860626779122035718023240315) * 10 ^ 70 +
        3721890242614846966716032168284236168390937687768527174657322014859347) * 10 ^ 70 +
        3988394167656769101294342017269131647947221459500616847714928818727905) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 9 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 17 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (323 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_323 :
    recurrence5Scalar0Main.coeff 323 =
      (((((274472756461046009456167087321017270610251930504173972227 * 10 ^ 70 +
        8858500905629877587990938714516856594377315253559677484761119676741898) * 10 ^ 70 +
        3127540028712140204660096017517127573670861076660284284983107994933749) * 10 ^ 70 +
        2259957272830779912564270894033055159184722908002646427612625257201457) * 10 ^ 70 +
        9036486762030961575313807938725613213047732320617443787700485538827706) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 10 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 16 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (324 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_324 :
    recurrence5Scalar0Main.coeff 324 =
      -(((((234551065821283221582252412606989007142550958840118790336 * 10 ^ 70 +
        4102317118348927073360334656817155709648935384038064789468713575176782) * 10 ^ 70 +
        5351348552451042803517780228031834741644126297114260140494319385205922) * 10 ^ 70 +
        5088274442305753591831931976317860811648546235280083104744116604890366) * 10 ^ 70 +
        9018903627354053817524193665346347827647310909664475845181075960261004) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 11 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 15 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (325 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_325 :
    recurrence5Scalar0Main.coeff 325 =
      (((((150486888119031806501531117923273634175101360389524805313 * 10 ^ 70 +
        4603864967058780765038771352807892629705172317064205488125742759124745) * 10 ^ 70 +
        4840710619246802413241629676434771892911328476415372752847818375470838) * 10 ^ 70 +
        0058327829637136159447356111909913191710093799240637863206326690292820) * 10 ^ 70 +
        1345932851859115638072507024584341603994280035823496315873106854306243) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 12 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 14 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (326 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_326 :
    recurrence5Scalar0Main.coeff 326 =
      -(((((85254880273976771391364856619000029849974890755106648015 * 10 ^ 70 +
        6813857503215766928746233816462228835712683750696462424740692917970925) * 10 ^ 70 +
        2584091336884760213561015077292356065811569454507666535239299145250273) * 10 ^ 70 +
        1921684646316812504965289422818447703725412129455712490416614932414624) * 10 ^ 70 +
        9782490600318311931994245649827448421918145741245558275600704946846331) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 13 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 13 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (327 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_327 :
    recurrence5Scalar0Main.coeff 327 =
      (((((44936867936440134751464998372148490709635246029414722733 * 10 ^ 70 +
        9576079497726444180519906757007149721691415855555654939417036289422275) * 10 ^ 70 +
        7494537228081768589138836681286785830627864468951983186806157078821834) * 10 ^ 70 +
        9950767934206852595318767260507140279905924459718555158831795657097370) * 10 ^ 70 +
        9377209450453055215711535123623199434543683492315101118591021360860037) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 14 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 12 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (328 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_328 :
    recurrence5Scalar0Main.coeff 328 =
      -(((((22569613063797856147225773421635581805311786883281022027 * 10 ^ 70 +
        0528711301127182834642304581680851083234526439080464880892204836854871) * 10 ^ 70 +
        5629923941867694901318216791344407464511141034578970327504375459299451) * 10 ^ 70 +
        2886732250996893984047595719151550989626930251807294154754709919476821) * 10 ^ 70 +
        1974869449554413024175981122254160733044907192148479863264591519044353) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 15 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 11 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (329 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_329 :
    recurrence5Scalar0Main.coeff 329 =
      (((((10943788571475073731680528780743448914171404571756963582 * 10 ^ 70 +
        8636197805159324378285277611813912760541195040905779955761557496384441) * 10 ^ 70 +
        5863715197521464045941490875124766669508297514273286855446947551022641) * 10 ^ 70 +
        6566530041691486506370045742999243484143817742290370369251759600046575) * 10 ^ 70 +
        5193406727438087940941339188189096152912937766777668644332441412442468) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 16 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 10 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (330 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_330 :
    recurrence5Scalar0Main.coeff 330 =
      -(((((5164086127416312815720030219587330540424699273514992035 * 10 ^ 70 +
        7847947880597813124128966724950397445952803207971562706979001269574324) * 10 ^ 70 +
        5276008116843209802910078125531224725073980302307902821076887917923762) * 10 ^ 70 +
        3137561972870933797941461257653161375852037889734701883636182904872883) * 10 ^ 70 +
        7147877039399639826296882814734883740404356987962968305921946010386666) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 17 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 9 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (331 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_331 :
    recurrence5Scalar0Main.coeff 331 =
      (((((2383524241346315948989825413288082228440776750219310036 * 10 ^ 70 +
        3970645345032149237276283514262174136475867038847422755140242659035284) * 10 ^ 70 +
        3089044596942851620184841951765760197726720047738821670550087582818302) * 10 ^ 70 +
        0115524435097170428606660994814376829743167470582436811713435691578621) * 10 ^ 70 +
        0438408004176761964812469367666371068779910098052354639046057623357109) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 18 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 8 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (332 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_332 :
    recurrence5Scalar0Main.coeff 332 =
      -(((((1079622631154934092998016436501371082841432582572070165 * 10 ^ 70 +
        3447166818616785541818843548042703305228272769558471576526978942473254) * 10 ^ 70 +
        0212226446332426989974833585632961154069767436709266671825860532351888) * 10 ^ 70 +
        6985752780514303755915388520864917073529283828985409032069176786224792) * 10 ^ 70 +
        0518310548432879559019665135361109319192553895872841068419592857810724) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 19 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 7 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (333 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_333 :
    recurrence5Scalar0Main.coeff 333 =
      (((((480859367652750027562602034827376265715357058646265933 * 10 ^ 70 +
        9324805478919996786204567842229959747344544567478693602864509610025416) * 10 ^ 70 +
        0549135054226914975664308565862078344288131547014391532721803701924441) * 10 ^ 70 +
        6708530350023714837813235459233375865115575730677222980776218359759639) * 10 ^ 70 +
        4488437158641365323110878432130611361497179183027569065240583829324281) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 20 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 6 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (334 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_334 :
    recurrence5Scalar0Main.coeff 334 =
      -(((((210818300234365191597517970764510321814051112135913949 * 10 ^ 70 +
        5953574171155671826028527155924456479581237436193787535469498650939054) * 10 ^ 70 +
        9700074516440042984485596734928896121934105863448530450848989154482579) * 10 ^ 70 +
        5275196733578758742331268906802575569233085798545503336083459861722426) * 10 ^ 70 +
        3959658799455164496935921550662924553761304272664864607393814711515922) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 21 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 5 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (335 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_335 :
    recurrence5Scalar0Main.coeff 335 =
      (((((91007756232421752604517083401853590969907117714799761 * 10 ^ 70 +
        5985946808770234461141716132133051211390954161416594077303595412839158) * 10 ^ 70 +
        1733674731586978786192039217899434191275590429267461424551848203743671) * 10 ^ 70 +
        4485725760297985707569922517872043870416592078839463824484295175060502) * 10 ^ 70 +
        2838060914124764977795267166798129584629116282792211949495346635082050) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 22 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 4 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (336 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_336 :
    recurrence5Scalar0Main.coeff 336 =
      -(((((38675269872823705631814210172705325432606102827228227 * 10 ^ 70 +
        9384410720944267067004934029977939174549733825627195713413650410222966) * 10 ^ 70 +
        1102952019984015186079402018547498656825249668918906982630379073030834) * 10 ^ 70 +
        2509091022402928297225270677933652225668621658238065134592596997122914) * 10 ^ 70 +
        8592296437579538546684744588913866267242713880660224228865781374984761) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 23 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 3 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (337 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_337 :
    recurrence5Scalar0Main.coeff 337 =
      (((((16170344529088840707035991471588711450694595702331299 * 10 ^ 70 +
        3785280277420442086426880735070635677812772771725079558627307369840421) * 10 ^ 70 +
        4387988711183503780324773629052692177348249195924275162695212491284915) * 10 ^ 70 +
        7715019526665964652101984207327869033386572085966681087516011066053806) * 10 ^ 70 +
        6722027435464634422246645457515553005999925168803365945187896781303665) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 24 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 2 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (338 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_338 :
    recurrence5Scalar0Main.coeff 338 =
      -(((((6646357345391990589873980274999034270275942817721674 * 10 ^ 70 +
        8206552704166840089172179052466680567841862808936275469362818660061539) * 10 ^ 70 +
        5449318942182964694145910849767182896210363827674753963617176125835132) * 10 ^ 70 +
        1295708000405656406642431125121267720870924498335333968610711338501465) * 10 ^ 70 +
        5409496030908431523924005472709228983523852050620381097759676886446154) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 25 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 1 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (339 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_339 :
    recurrence5Scalar0Main.coeff 339 =
      (((((2683013380076624365589390630382915085175777860574192 * 10 ^ 70 +
        5311887831277130821034085640336663527954412666419526031012658740949778) * 10 ^ 70 +
        9519342747150664148683741412874819369347581947040861405951938768622514) * 10 ^ 70 +
        3439070870045670106812098519975140401874503933934866058748491729305426) * 10 ^ 70 +
        4140436586945502607102837367340592275633310657793613035946715993187988) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 26 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (340 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_340 :
    recurrence5Scalar0Main.coeff 340 =
      -(((((1062711968951584695708929105054550428615221388143248 * 10 ^ 70 +
        3159167105032165531248517800472964386025295315492503827121035107592690) * 10 ^ 70 +
        3564651494302620467206653715849979071489083859594692717050376804992342) * 10 ^ 70 +
        8582625551029102708319690827129583849126523453926592513328064250712184) * 10 ^ 70 +
        8680487875019425458320380620090171263302235868530888161406273670447404) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 27 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 31 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (341 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_341 :
    recurrence5Scalar0Main.coeff 341 =
      (((((412614423602051147332769585116830194933310297003152 * 10 ^ 70 +
        7027576619837143324751097814215094352940309553195608177194191883688308) * 10 ^ 70 +
        3901458489216989482043798679759224215260775806664413838512161314616541) * 10 ^ 70 +
        1765867390105823159330281927028139863739567168390905267216541188325166) * 10 ^ 70 +
        3274891902216062892143282737870304071331569098018983270382945719757224) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 28 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 30 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (342 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_342 :
    recurrence5Scalar0Main.coeff 342 =
      -(((((156893598880308479146161843550886527954486325079394 * 10 ^ 70 +
        7540148030758026237456251321519120761686027282542259270505864823882649) * 10 ^ 70 +
        4586283771698366000697235413542726981935735433985267655978366854259117) * 10 ^ 70 +
        0174058310701873179109067048082680126259928054952449466215752576494867) * 10 ^ 70 +
        8147453832263612487009603878071830735008708642382009439453239584890892) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 29 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 29 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (343 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_343 :
    recurrence5Scalar0Main.coeff 343 =
      (((((58372351227104008884886475990617311145099943910678 * 10 ^ 70 +
        3775670328312124147006468825137356486808451961986596433646026084798947) * 10 ^ 70 +
        4576939653390862384925275857866862797007679204966536371495712283219020) * 10 ^ 70 +
        5873869483534466255343263947440749734146647161466649669044446331060214) * 10 ^ 70 +
        6586770590761164986502330456903060245198068536432951144777540405651937) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 30 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 28 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (344 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_344 :
    recurrence5Scalar0Main.coeff 344 =
      -(((((21230677262887106905479756858647388834658369646683 * 10 ^ 70 +
        0243661061775176010288841598063915229280703989238375935020490683460912) * 10 ^ 70 +
        8983769880502432682921488507881084756202147000704291578788538774832612) * 10 ^ 70 +
        5494059009814436437969256627555874135269540005186308583282049275527353) * 10 ^ 70 +
        4291959379962129929939970834006649078103082109794699496160239256995111) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 31 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 27 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (345 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_345 :
    recurrence5Scalar0Main.coeff 345 =
      (((((7541807321178365365552515665946004264542122140401 * 10 ^ 70 +
        3767422017245795064243151106182905344725070791766978343340012200473850) * 10 ^ 70 +
        1896792635638540515923728402913662337382297121864148174563659534393328) * 10 ^ 70 +
        5376589518640663630883087632855896582785525604700509696621147895158073) * 10 ^ 70 +
        7559732202506880530612087286755075925111214046119664638969379551345398) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 32 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 26 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (346 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_346 :
    recurrence5Scalar0Main.coeff 346 =
      -(((((2613968617029313797429993472780248232207423295706 * 10 ^ 70 +
        2348823473497993947865069047562269077263530781414300859475455739834814) * 10 ^ 70 +
        8809961827692486204749082262538030815704780963500266046582902278358290) * 10 ^ 70 +
        6541893722139710353671760015691952868239447085337946923791726978900332) * 10 ^ 70 +
        1129238511750199063804642970268372332945957667297923004792553932852928) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 33 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 25 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (347 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_347 :
    recurrence5Scalar0Main.coeff 347 =
      (((((882900013131906372030113835408277389698106501619 * 10 ^ 70 +
        7881287970146205121758166108920389585064735822528056396741997210596653) * 10 ^ 70 +
        9416730190804445513444354400175620144606318677692395220012865810146456) * 10 ^ 70 +
        5939124319053969597483022201346519085484978320458309819075619296252319) * 10 ^ 70 +
        7645421336404721700643872454687579424335777685982865555203306198916195) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 34 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 24 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (348 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_348 :
    recurrence5Scalar0Main.coeff 348 =
      -(((((290153530169998064731747449877791111073942102817 * 10 ^ 70 +
        9717014674366660890304181840010068343294326611919262478440005187151738) * 10 ^ 70 +
        3873634491769555637709919201854205361666097070229668403721871019517848) * 10 ^ 70 +
        9405070151869146957955313510546138509026202984212941127833838054381541) * 10 ^ 70 +
        9373668628761999958159490754354629715649184661732844183523925163423435) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 35 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 23 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (349 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_349 :
    recurrence5Scalar0Main.coeff 349 =
      (((((92577052133871547668790349602065173814220948371 * 10 ^ 70 +
        2997078516662588993182929085364042226543377395775479038657279143561721) * 10 ^ 70 +
        7252967805019256406729805014890645901311801643679600027434065445036813) * 10 ^ 70 +
        9161315233084397112423937703659936498163912308417666136030448193765577) * 10 ^ 70 +
        7712969448409425094505518731545662805416700720819480512394411508856224) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 36 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 22 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (350 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_350 :
    recurrence5Scalar0Main.coeff 350 =
      -(((((28584861005342224097261074285594851541693611666 * 10 ^ 70 +
        8542784118859072268580506206160718117036911742972625902596254986030379) * 10 ^ 70 +
        0517120771686307260028654710926515527476483224720615642347151738943060) * 10 ^ 70 +
        6359878786793024953839939668648099693618693201180312627289172880888848) * 10 ^ 70 +
        2149906164620786066318667522025403408350208564083562287721829358814403) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 37 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 21 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (351 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_351 :
    recurrence5Scalar0Main.coeff 351 =
      (((((8497995653686911286880609445215429096817931015 * 10 ^ 70 +
        0087607117800142041002867462812588104131526290392331536122442971308212) * 10 ^ 70 +
        7949670689102781687562599935288814332750082052627872519422685632261815) * 10 ^ 70 +
        1188938318102690464588425656535529872795338585648113713967196281851442) * 10 ^ 70 +
        5420218728300856248128389178050872895021949954965875051573744332848952) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 38 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 20 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (352 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_352 :
    recurrence5Scalar0Main.coeff 352 =
      -(((((2411671151680648316712715883645330650528471209 * 10 ^ 70 +
        6419807883745864910951149715983738575392431218829733225883724657700925) * 10 ^ 70 +
        5086599066983374037298935369915258869354023674971192805043234504833908) * 10 ^ 70 +
        4907067320491816109259530273621940920328398743054723214887038528006685) * 10 ^ 70 +
        8896500805853605807024735483592098516542690675298275512229234851979394) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 39 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 19 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (353 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_353 :
    recurrence5Scalar0Main.coeff 353 =
      (((((643104981430192337720450924061267886952096764 * 10 ^ 70 +
        7214043412023067951394621140190366444294233389788836483974248799512283) * 10 ^ 70 +
        5482144124768874365324904885795733646870781538218251108104675862077529) * 10 ^ 70 +
        1073557300099449767724776880072697381447904141241800699788463052629288) * 10 ^ 70 +
        1664174958404519067951853126055303742311401453157847489887239082949773) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 40 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 18 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (354 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_354 :
    recurrence5Scalar0Main.coeff 354 =
      -(((((155889296192914221670387699287256197642352541 * 10 ^ 70 +
        0347281105497207367690554491079222572483945158810739674124078234488819) * 10 ^ 70 +
        2375477019356485275475893129794532322912293746282111038431515892684827) * 10 ^ 70 +
        9515436932686770345348971367992523553528859467888639670842818982692898) * 10 ^ 70 +
        1039387229191554757763027786567978414067784916562143264895741650434891) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 41 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 17 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (355 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_355 :
    recurrence5Scalar0Main.coeff 355 =
      (((((31466082230723548792126647010414872970415677 * 10 ^ 70 +
        6658468964691010408138434471508206632960000115736379102709400485780395) * 10 ^ 70 +
        3665343552025719145262449006588293014606750556652488031715217662718870) * 10 ^ 70 +
        8726230084211166913000656465964198102961747915005481609041605824308874) * 10 ^ 70 +
        7070457771727406643212191081208632400688081875606280041947758051930497) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 42 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 16 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (356 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_356 :
    recurrence5Scalar0Main.coeff 356 =
      -(((((3504658466625329799962385636280659610350655 * 10 ^ 70 +
        2893556412664629592505110634208218985549789307333880586149531669145491) * 10 ^ 70 +
        7498843613602489016277709982569693877557709852365584269593706802592900) * 10 ^ 70 +
        0491832414839233224126002292956149446196918552017085776979213309535511) * 10 ^ 70 +
        2629029010024061013444558604944886839149712032417732185991806179424671) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 43 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 15 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (357 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_357 :
    recurrence5Scalar0Main.coeff 357 =
      -(((((1161687644433421417556988157405784685736816 * 10 ^ 70 +
        7460314231176602246798653502760713394906021771877468817183137020256337) * 10 ^ 70 +
        4188161347512674112559610469008694929507132544240233241689008356886650) * 10 ^ 70 +
        9443693328864391815500391599939605174769216439250922473400735772182025) * 10 ^ 70 +
        0411343622994416723338190774278182514328741321863611234235605731332752) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 44 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 14 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (358 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_358 :
    recurrence5Scalar0Main.coeff 358 =
      (((((1152860365448186011844101538180976396125895 * 10 ^ 70 +
        6295227307324304911954750905998186070871703497263532798353410069823402) * 10 ^ 70 +
        9946555883975417695107126015400802144722208413007575192567658659637527) * 10 ^ 70 +
        7283600538083587949957234818221754775359412667384509373498809677424674) * 10 ^ 70 +
        0012634130195725558871866437190305468957488293584767994895700032401462) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 45 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 13 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (359 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_359 :
    recurrence5Scalar0Main.coeff 359 =
      -(((((633346122229111887427306086903589046895582 * 10 ^ 70 +
        9773683112093155188963359638500936959627363511925919054297496462291667) * 10 ^ 70 +
        2258837758629532904859586823115358692663910835791551555780848418406704) * 10 ^ 70 +
        7850718549597907612395487647431051773205625263712690953724001434801633) * 10 ^ 70 +
        2809195712845565105931048785466214136540077822965980890771993582443498) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 46 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 12 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (360 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_360 :
    recurrence5Scalar0Main.coeff 360 =
      (((((291591997527274660733073155593569535067494 * 10 ^ 70 +
        9280876470524607996693817677210912879992611035850157368620597413731168) * 10 ^ 70 +
        9005209868933650328886007154923800164480418077018621723374802731976504) * 10 ^ 70 +
        9272028360549822116770601829968504273775445117964824500720969302371877) * 10 ^ 70 +
        4881210676224664743031006849078124170682166200100638878860590892109375) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 47 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 11 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (361 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_361 :
    recurrence5Scalar0Main.coeff 361 =
      -(((((123058870246476339003122077118940589701292 * 10 ^ 70 +
        6710642952241946738160239882093003524090891369260876617921213576818941) * 10 ^ 70 +
        5362000803018241198031405212594746400590289311062126867139750495561064) * 10 ^ 70 +
        3149757336934527788597089456584553351757878111516309510553469702556127) * 10 ^ 70 +
        3467806611926069605297870903530447623726733243449284921697847741936379) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 48 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 10 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (362 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_362 :
    recurrence5Scalar0Main.coeff 362 =
      (((((49272167326149971273234548828355645898603 * 10 ^ 70 +
        3466972568350037756719181225939422381830489025971740856340925632329742) * 10 ^ 70 +
        8168919330295318781943074783433125040316858081310229072403456550386704) * 10 ^ 70 +
        5540092553194064937862755178144191687377242473013430998550073235641576) * 10 ^ 70 +
        2591606438175671916973218684402330564238494413739094430559294601812989) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 49 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 9 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (363 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_363 :
    recurrence5Scalar0Main.coeff 363 =
      -(((((19026785410374987774805671900645965871412 * 10 ^ 70 +
        0853058229733565807898689788659862816294435433781247856505566479075354) * 10 ^ 70 +
        3432280628858943556983487198884008345161589061607901474499196136074129) * 10 ^ 70 +
        9118616641760656160970309113207754075145948724668070230428079720222277) * 10 ^ 70 +
        4821758499748885089216526516888252814220501915273128247317884401621639) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 50 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 8 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
