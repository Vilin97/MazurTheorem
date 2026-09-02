/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B2_coeff_0
  recurrence4B2_coeff_1
  recurrence4B2_coeff_10
  recurrence4B2_coeff_100
  recurrence4B2_coeff_101
  recurrence4B2_coeff_102
  recurrence4B2_coeff_103
  recurrence4B2_coeff_104
  recurrence4B2_coeff_105
  recurrence4B2_coeff_106
  recurrence4B2_coeff_107
  recurrence4B2_coeff_108
  recurrence4B2_coeff_109
  recurrence4B2_coeff_11
  recurrence4B2_coeff_110
  recurrence4B2_coeff_111
  recurrence4B2_coeff_112
  recurrence4B2_coeff_113
  recurrence4B2_coeff_114
  recurrence4B2_coeff_115
  recurrence4B2_coeff_116
  recurrence4B2_coeff_117
  recurrence4B2_coeff_118
  recurrence4B2_coeff_119
  recurrence4B2_coeff_12
  recurrence4B2_coeff_120
  recurrence4B2_coeff_121
  recurrence4B2_coeff_122
  recurrence4B2_coeff_123
  recurrence4B2_coeff_124
  recurrence4B2_coeff_125
  recurrence4B2_coeff_126
  recurrence4B2_coeff_127
  recurrence4B2_coeff_128
  recurrence4B2_coeff_129
  recurrence4B2_coeff_13
  recurrence4B2_coeff_130
  recurrence4B2_coeff_131
  recurrence4B2_coeff_132
  recurrence4B2_coeff_133
  recurrence4B2_coeff_134
  recurrence4B2_coeff_135
  recurrence4B2_coeff_136
  recurrence4B2_coeff_137
  recurrence4B2_coeff_138
  recurrence4B2_coeff_139
  recurrence4B2_coeff_14
  recurrence4B2_coeff_140
  recurrence4B2_coeff_141
  recurrence4B2_coeff_142
  recurrence4B2_coeff_143
  recurrence4B2_coeff_144
  recurrence4B2_coeff_145
  recurrence4B2_coeff_146
  recurrence4B2_coeff_147
  recurrence4B2_coeff_148
  recurrence4B2_coeff_149
  recurrence4B2_coeff_15
  recurrence4B2_coeff_150
  recurrence4B2_coeff_151
  recurrence4B2_coeff_152
  recurrence4B2_coeff_153
  recurrence4B2_coeff_154
  recurrence4B2_coeff_155

attribute [local simp]
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157
  recurrence4B2_coeff_158
  recurrence4B2_coeff_159
  recurrence4B2_coeff_16
  recurrence4B2_coeff_160
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167
  recurrence4B2_coeff_168
  recurrence4B2_coeff_17
  recurrence4B2_coeff_18
  recurrence4B2_coeff_19
  recurrence4B2_coeff_2
  recurrence4B2_coeff_20
  recurrence4B2_coeff_21
  recurrence4B2_coeff_22
  recurrence4B2_coeff_23
  recurrence4B2_coeff_24
  recurrence4B2_coeff_25
  recurrence4B2_coeff_26
  recurrence4B2_coeff_27
  recurrence4B2_coeff_28
  recurrence4B2_coeff_29
  recurrence4B2_coeff_3
  recurrence4B2_coeff_30
  recurrence4B2_coeff_31
  recurrence4B2_coeff_32
  recurrence4B2_coeff_33
  recurrence4B2_coeff_34
  recurrence4B2_coeff_35
  recurrence4B2_coeff_36
  recurrence4B2_coeff_37
  recurrence4B2_coeff_38
  recurrence4B2_coeff_39
  recurrence4B2_coeff_4
  recurrence4B2_coeff_40
  recurrence4B2_coeff_41
  recurrence4B2_coeff_42
  recurrence4B2_coeff_43
  recurrence4B2_coeff_44
  recurrence4B2_coeff_45
  recurrence4B2_coeff_46
  recurrence4B2_coeff_47
  recurrence4B2_coeff_48
  recurrence4B2_coeff_49
  recurrence4B2_coeff_5
  recurrence4B2_coeff_50
  recurrence4B2_coeff_51
  recurrence4B2_coeff_52
  recurrence4B2_coeff_53
  recurrence4B2_coeff_54
  recurrence4B2_coeff_55
  recurrence4B2_coeff_56
  recurrence4B2_coeff_57
  recurrence4B2_coeff_58
  recurrence4B2_coeff_59
  recurrence4B2_coeff_6
  recurrence4B2_coeff_60
  recurrence4B2_coeff_61

attribute [local simp]
  recurrence4B2_coeff_62
  recurrence4B2_coeff_63
  recurrence4B2_coeff_64
  recurrence4B2_coeff_65
  recurrence4B2_coeff_66
  recurrence4B2_coeff_67
  recurrence4B2_coeff_68
  recurrence4B2_coeff_69
  recurrence4B2_coeff_7
  recurrence4B2_coeff_70
  recurrence4B2_coeff_71
  recurrence4B2_coeff_72
  recurrence4B2_coeff_73
  recurrence4B2_coeff_74
  recurrence4B2_coeff_75
  recurrence4B2_coeff_76
  recurrence4B2_coeff_77
  recurrence4B2_coeff_78
  recurrence4B2_coeff_79
  recurrence4B2_coeff_8
  recurrence4B2_coeff_80
  recurrence4B2_coeff_81
  recurrence4B2_coeff_82
  recurrence4B2_coeff_83
  recurrence4B2_coeff_84
  recurrence4B2_coeff_85
  recurrence4B2_coeff_86
  recurrence4B2_coeff_87
  recurrence4B2_coeff_88
  recurrence4B2_coeff_89
  recurrence4B2_coeff_9
  recurrence4B2_coeff_90
  recurrence4B2_coeff_91
  recurrence4B2_coeff_92
  recurrence4B2_coeff_93
  recurrence4B2_coeff_94
  recurrence4B2_coeff_95
  recurrence4B2_coeff_96
  recurrence4B2_coeff_97
  recurrence4B2_coeff_98
  recurrence4B2_coeff_99
  recurrence4QuotientConstant_coeff_100
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115
  recurrence4QuotientConstant_coeff_116
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122

attribute [local simp]
  recurrence4QuotientConstant_coeff_123
  recurrence4QuotientConstant_coeff_124
  recurrence4QuotientConstant_coeff_125
  recurrence4QuotientConstant_coeff_126
  recurrence4QuotientConstant_coeff_127
  recurrence4QuotientConstant_coeff_128
  recurrence4QuotientConstant_coeff_129
  recurrence4QuotientConstant_coeff_130
  recurrence4QuotientConstant_coeff_131
  recurrence4QuotientConstant_coeff_132
  recurrence4QuotientConstant_coeff_133
  recurrence4QuotientConstant_coeff_134
  recurrence4QuotientConstant_coeff_135
  recurrence4QuotientConstant_coeff_136
  recurrence4QuotientConstant_coeff_137
  recurrence4QuotientConstant_coeff_138
  recurrence4QuotientConstant_coeff_139
  recurrence4QuotientConstant_coeff_140
  recurrence4QuotientConstant_coeff_141
  recurrence4QuotientConstant_coeff_142
  recurrence4QuotientConstant_coeff_143
  recurrence4QuotientConstant_coeff_144
  recurrence4QuotientConstant_coeff_145
  recurrence4QuotientConstant_coeff_146
  recurrence4QuotientConstant_coeff_147
  recurrence4QuotientConstant_coeff_148
  recurrence4QuotientConstant_coeff_149
  recurrence4QuotientConstant_coeff_150
  recurrence4QuotientConstant_coeff_151
  recurrence4QuotientConstant_coeff_152
  recurrence4QuotientConstant_coeff_153
  recurrence4QuotientConstant_coeff_154
  recurrence4QuotientConstant_coeff_155
  recurrence4QuotientConstant_coeff_156
  recurrence4QuotientConstant_coeff_157
  recurrence4QuotientConstant_coeff_158
  recurrence4QuotientConstant_coeff_159
  recurrence4QuotientConstant_coeff_160
  recurrence4QuotientConstant_coeff_161
  recurrence4QuotientConstant_coeff_162
  recurrence4QuotientConstant_coeff_163
  recurrence4QuotientConstant_coeff_164
  recurrence4QuotientConstant_coeff_165
  recurrence4QuotientConstant_coeff_166
  recurrence4QuotientConstant_coeff_167
  recurrence4QuotientConstant_coeff_168
  recurrence4QuotientConstant_coeff_169
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_180
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186

attribute [local simp]
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
  recurrence4QuotientConstant_coeff_209
  recurrence4QuotientConstant_coeff_210
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_217
  recurrence4QuotientConstant_coeff_218
  recurrence4QuotientConstant_coeff_219
  recurrence4QuotientConstant_coeff_220
  recurrence4QuotientConstant_coeff_221
  recurrence4QuotientConstant_coeff_222
  recurrence4QuotientConstant_coeff_223
  recurrence4QuotientConstant_coeff_224
  recurrence4QuotientConstant_coeff_225
  recurrence4QuotientConstant_coeff_226
  recurrence4QuotientConstant_coeff_227
  recurrence4QuotientConstant_coeff_228
  recurrence4QuotientConstant_coeff_229
  recurrence4QuotientConstant_coeff_230
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_240
  recurrence4QuotientConstant_coeff_241
  recurrence4QuotientConstant_coeff_242
  recurrence4QuotientConstant_coeff_243
  recurrence4QuotientConstant_coeff_244
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_250

attribute [local simp]
  recurrence4QuotientConstant_coeff_251
  recurrence4QuotientConstant_coeff_252
  recurrence4QuotientConstant_coeff_253
  recurrence4QuotientConstant_coeff_254
  recurrence4QuotientConstant_coeff_255
  recurrence4QuotientConstant_coeff_256
  recurrence4QuotientConstant_coeff_257
  recurrence4QuotientConstant_coeff_258
  recurrence4QuotientConstant_coeff_259
  recurrence4QuotientConstant_coeff_260
  recurrence4QuotientConstant_coeff_261
  recurrence4QuotientConstant_coeff_262
  recurrence4QuotientConstant_coeff_263
  recurrence4QuotientConstant_coeff_264
  recurrence4QuotientConstant_coeff_265
  recurrence4QuotientConstant_coeff_266
  recurrence4QuotientConstant_coeff_267
  recurrence4QuotientConstant_coeff_268
  recurrence4QuotientConstant_coeff_269
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_275
  recurrence4QuotientConstant_coeff_276
  recurrence4QuotientConstant_coeff_277
  recurrence4QuotientConstant_coeff_278
  recurrence4QuotientConstant_coeff_279
  recurrence4QuotientConstant_coeff_280
  recurrence4QuotientConstant_coeff_281
  recurrence4QuotientConstant_coeff_282
  recurrence4QuotientConstant_coeff_283
  recurrence4QuotientConstant_coeff_284
  recurrence4QuotientConstant_coeff_285
  recurrence4QuotientConstant_coeff_286
  recurrence4QuotientConstant_coeff_287
  recurrence4QuotientConstant_coeff_288
  recurrence4QuotientConstant_coeff_289
  recurrence4QuotientConstant_coeff_290
  recurrence4QuotientConstant_coeff_291
  recurrence4QuotientConstant_coeff_292
  recurrence4QuotientConstant_coeff_293
  recurrence4QuotientConstant_coeff_294
  recurrence4QuotientConstant_coeff_295
  recurrence4QuotientConstant_coeff_296
  recurrence4QuotientConstant_coeff_297
  recurrence4QuotientConstant_coeff_298
  recurrence4QuotientConstant_coeff_299
  recurrence4QuotientConstant_coeff_300
  recurrence4QuotientConstant_coeff_301
  recurrence4QuotientConstant_coeff_302
  recurrence4QuotientConstant_coeff_303
  recurrence4QuotientConstant_coeff_304
  recurrence4QuotientConstant_coeff_305
  recurrence4QuotientConstant_coeff_306
  recurrence4QuotientConstant_coeff_307
  recurrence4QuotientConstant_coeff_308
  recurrence4QuotientConstant_coeff_309
  recurrence4QuotientConstant_coeff_310
  recurrence4QuotientConstant_coeff_311
  recurrence4QuotientConstant_coeff_312
  recurrence4QuotientConstant_coeff_313
  recurrence4QuotientConstant_coeff_314

attribute [local simp]
  recurrence4QuotientConstant_coeff_315
  recurrence4QuotientConstant_coeff_316
  recurrence4QuotientConstant_coeff_317
  recurrence4QuotientConstant_coeff_318
  recurrence4QuotientConstant_coeff_319
  recurrence4QuotientConstant_coeff_320
  recurrence4QuotientConstant_coeff_321
  recurrence4QuotientConstant_coeff_322
  recurrence4QuotientConstant_coeff_323
  recurrence4QuotientConstant_coeff_324
  recurrence4QuotientConstant_coeff_325
  recurrence4QuotientConstant_coeff_326
  recurrence4QuotientConstant_coeff_327
  recurrence4QuotientConstant_coeff_328
  recurrence4QuotientConstant_coeff_329
  recurrence4QuotientConstant_coeff_330
  recurrence4QuotientConstant_coeff_331
  recurrence4QuotientConstant_coeff_332
  recurrence4QuotientConstant_coeff_333
  recurrence4QuotientConstant_coeff_334
  recurrence4QuotientConstant_coeff_335
  recurrence4QuotientConstant_coeff_336
  recurrence4QuotientConstant_coeff_337
  recurrence4QuotientConstant_coeff_338
  recurrence4QuotientConstant_coeff_339
  recurrence4QuotientConstant_coeff_340
  recurrence4QuotientConstant_coeff_341
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346
  recurrence4QuotientConstant_coeff_49
  recurrence4QuotientConstant_coeff_50
  recurrence4QuotientConstant_coeff_51
  recurrence4QuotientConstant_coeff_52
  recurrence4QuotientConstant_coeff_53
  recurrence4QuotientConstant_coeff_54
  recurrence4QuotientConstant_coeff_55
  recurrence4QuotientConstant_coeff_56
  recurrence4QuotientConstant_coeff_57
  recurrence4QuotientConstant_coeff_58
  recurrence4QuotientConstant_coeff_59
  recurrence4QuotientConstant_coeff_60
  recurrence4QuotientConstant_coeff_61
  recurrence4QuotientConstant_coeff_62
  recurrence4QuotientConstant_coeff_63
  recurrence4QuotientConstant_coeff_64
  recurrence4QuotientConstant_coeff_65
  recurrence4QuotientConstant_coeff_66
  recurrence4QuotientConstant_coeff_67
  recurrence4QuotientConstant_coeff_68
  recurrence4QuotientConstant_coeff_69
  recurrence4QuotientConstant_coeff_70
  recurrence4QuotientConstant_coeff_71
  recurrence4QuotientConstant_coeff_72
  recurrence4QuotientConstant_coeff_73
  recurrence4QuotientConstant_coeff_74
  recurrence4QuotientConstant_coeff_75
  recurrence4QuotientConstant_coeff_76
  recurrence4QuotientConstant_coeff_77
  recurrence4QuotientConstant_coeff_78
  recurrence4QuotientConstant_coeff_79
  recurrence4QuotientConstant_coeff_80

attribute [local simp]
  recurrence4QuotientConstant_coeff_81
  recurrence4QuotientConstant_coeff_82
  recurrence4QuotientConstant_coeff_83
  recurrence4QuotientConstant_coeff_84
  recurrence4QuotientConstant_coeff_85
  recurrence4QuotientConstant_coeff_86
  recurrence4QuotientConstant_coeff_87
  recurrence4QuotientConstant_coeff_88
  recurrence4QuotientConstant_coeff_89
  recurrence4QuotientConstant_coeff_90
  recurrence4QuotientConstant_coeff_91
  recurrence4QuotientConstant_coeff_92
  recurrence4QuotientConstant_coeff_93
  recurrence4QuotientConstant_coeff_94
  recurrence4QuotientConstant_coeff_95
  recurrence4QuotientConstant_coeff_96
  recurrence4QuotientConstant_coeff_97
  recurrence4QuotientConstant_coeff_98
  recurrence4QuotientConstant_coeff_99

private theorem recurrence4Scalar2Second_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (324 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_324 :
    recurrence4Scalar2Second.coeff 324 =
      (((((5595251916595250 * 10 ^ 70 +
        6392472924244193114591568797391894523767428714520017310922666554081906) * 10 ^ 70 +
        7197352551908097896614114060546634965438390275372483622717089744129929) * 10 ^ 70 +
        1761747720407930790068065838958424522124251563810791063497154401678955) * 10 ^ 70 +
        2488725130975693685424182028977377179721208114955341864084015555273971) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (324 - x)) = _
  rw [show 325 = 0 +
    325 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 325 = 32 +
      293 by norm_num, Finset.sum_range_add]
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
    rw [show 165 = 9 +
      156 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (325 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_325 :
    recurrence4Scalar2Second.coeff 325 =
      -(((((4156731585505111 * 10 ^ 70 +
        0970253666082392256342218977380132493093444798588434074512824723672930) * 10 ^ 70 +
        4376359596143995063804537043008226275727904968106846306671959502224468) * 10 ^ 70 +
        1642015424850294992710028544215393162283384257709150610195914961481995) * 10 ^ 70 +
        5424675727249958079266576704743375207518470133172749624090208067227094) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (325 - x)) = _
  rw [show 326 = 0 +
    326 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 326 = 32 +
      294 by norm_num, Finset.sum_range_add]
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
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (326 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_326 :
    recurrence4Scalar2Second.coeff 326 =
      (((((2768598458179420 * 10 ^ 70 +
        6116890019114472411163901839975792339876007292106554661880813881137028) * 10 ^ 70 +
        7546585397509119839203387384106060355418296463778465605403765288086440) * 10 ^ 70 +
        5702463254480043670583978851749491238179900884225304450859609521810846) * 10 ^ 70 +
        2120777962212007449913021967888781855184145029064747587217693397042240) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (326 - x)) = _
  rw [show 327 = 0 +
    327 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 327 = 32 +
      295 by norm_num, Finset.sum_range_add]
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
    rw [show 167 = 9 +
      158 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (327 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_327 :
    recurrence4Scalar2Second.coeff 327 =
      -(((((1722236880824795 * 10 ^ 70 +
        3363293753995463065839534859408644346350252724859190951397593218480547) * 10 ^ 70 +
        9438714612599624797736226884928613397215550374644038579839203484209070) * 10 ^ 70 +
        8139856384187547814256690730794153170912063780001992062741822095732873) * 10 ^ 70 +
        2979818948404754324621133772744790122384612853209077592122442212065007) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (327 - x)) = _
  rw [show 328 = 0 +
    328 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 328 = 32 +
      296 by norm_num, Finset.sum_range_add]
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
    rw [show 168 = 9 +
      159 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (328 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_328 :
    recurrence4Scalar2Second.coeff 328 =
      (((((1020124856907655 * 10 ^ 70 +
        6861631587951893636812048182642098938271996472167830645235540279979161) * 10 ^ 70 +
        8060084185777976210782033151297924746182065696167647170588224404536329) * 10 ^ 70 +
        4251517843512103965539781760804130878028320286168998018353942585264825) * 10 ^ 70 +
        5593653282556290767408172289978629180716447710909414782402816375976899) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (328 - x)) = _
  rw [show 329 = 0 +
    329 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 329 = 32 +
      297 by norm_num, Finset.sum_range_add]
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
    rw [show 169 = 9 +
      160 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (329 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_329 :
    recurrence4Scalar2Second.coeff 329 =
      -(((((581529206173517 * 10 ^ 70 +
        6676886006125744247710067395788723747874630597529604971862471837206173) * 10 ^ 70 +
        6090090587204439184650061106234599839571724263221590993632246429260266) * 10 ^ 70 +
        9003783868899086586794484934048429055285103564670962923902918777564211) * 10 ^ 70 +
        2447848049009486565215051802975881272903357391230923327082340745287576) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (329 - x)) = _
  rw [show 330 = 0 +
    330 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 330 = 32 +
      298 by norm_num, Finset.sum_range_add]
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
    rw [show 170 = 9 +
      161 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (330 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_330 :
    recurrence4Scalar2Second.coeff 330 =
      (((((321110475621484 * 10 ^ 70 +
        6790727226620639350057560034133821121359388232442027827176683533103012) * 10 ^ 70 +
        3024497010567570310149153825396166436314837780374766673904009222319771) * 10 ^ 70 +
        5419198136539314686476377953957958062274178880330630015926334671791653) * 10 ^ 70 +
        5253079958033371496288417148455176405555946734916099454721421299577586) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (330 - x)) = _
  rw [show 331 = 0 +
    331 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 331 = 32 +
      299 by norm_num, Finset.sum_range_add]
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
    rw [show 171 = 9 +
      162 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (331 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_331 :
    recurrence4Scalar2Second.coeff 331 =
      -(((((172470827633458 * 10 ^ 70 +
        6159431687405218503186130601316560823351750632773608782905144584915806) * 10 ^ 70 +
        3512631755551514345808436700908190012732591891799515995586902131011530) * 10 ^ 70 +
        4754912612024415739389040845472986889961405623245392715504924819435165) * 10 ^ 70 +
        6430226599912141015256430030575792304816715476045047868797744036166948) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (331 - x)) = _
  rw [show 332 = 0 +
    332 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 332 = 32 +
      300 by norm_num, Finset.sum_range_add]
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
    rw [show 172 = 9 +
      163 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (332 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_332 :
    recurrence4Scalar2Second.coeff 332 =
      (((((90360310814198 * 10 ^ 70 +
        6875240617517991035165933512211510092242348133586292810900418302209145) * 10 ^ 70 +
        3949034725514341787129713896197980084942972744488618131215547752126836) * 10 ^ 70 +
        5691101346135580791307529402918234815711636305207631704570727480961995) * 10 ^ 70 +
        4948546503268905536761849908959478306456855837972649359190664158814576) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (332 - x)) = _
  rw [show 333 = 0 +
    333 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 333 = 32 +
      301 by norm_num, Finset.sum_range_add]
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
    rw [show 173 = 9 +
      164 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (333 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_333 :
    recurrence4Scalar2Second.coeff 333 =
      -(((((46268694131063 * 10 ^ 70 +
        2519797250806601397543797261113626432701007898278811317299927683119417) * 10 ^ 70 +
        1988935449960526514989483946008358288053527778820544047467337604538234) * 10 ^ 70 +
        4866853804710560498825841812151087954459547059340715717968876091000926) * 10 ^ 70 +
        5607684525848754477455864098587000735068331324300249158098902189289263) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (333 - x)) = _
  rw [show 334 = 0 +
    334 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 334 = 32 +
      302 by norm_num, Finset.sum_range_add]
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
    rw [show 174 = 9 +
      165 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (334 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_334 :
    recurrence4Scalar2Second.coeff 334 =
      (((((23186629355552 * 10 ^ 70 +
        5812557417184280824094622001268641253599551961637587735500204992439476) * 10 ^ 70 +
        5972968574737526331139581988658382067752234425099794010360475854573424) * 10 ^ 70 +
        6859695278425864328505996061394055040636635248512318126848175416435048) * 10 ^ 70 +
        4338891958532632069276713687775650726035533072584883470601926133523601) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (334 - x)) = _
  rw [show 335 = 0 +
    335 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 335 = 32 +
      303 by norm_num, Finset.sum_range_add]
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
    rw [show 175 = 9 +
      166 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (335 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_335 :
    recurrence4Scalar2Second.coeff 335 =
      -(((((11382651761788 * 10 ^ 70 +
        2245172678443245556464113590417833848449832183134968523546318918721728) * 10 ^ 70 +
        5274425652230567798229949502000918177165594212942156570150218885927870) * 10 ^ 70 +
        2653507857219412079263794243330413864502627295099041114399844630774102) * 10 ^ 70 +
        9839137043166353074145300641353290373807921735429922199549708573131829) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (335 - x)) = _
  rw [show 336 = 0 +
    336 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 336 = 32 +
      304 by norm_num, Finset.sum_range_add]
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
    rw [show 176 = 9 +
      167 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (336 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_336 :
    recurrence4Scalar2Second.coeff 336 =
      (((((5477565124270 * 10 ^ 70 +
        6496879069400333190084478268024758349383255560863375953509757950291366) * 10 ^ 70 +
        4675101167263509894336911031872298198435094492656816524855545730979729) * 10 ^ 70 +
        3272715467359010690104339190090805053766236797811296017133319886245927) * 10 ^ 70 +
        3793796695669134151869616919504639223987136292531366349115532896918749) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (336 - x)) = _
  rw [show 337 = 0 +
    337 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 337 = 32 +
      305 by norm_num, Finset.sum_range_add]
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
    rw [show 177 = 9 +
      168 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (337 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_337 :
    recurrence4Scalar2Second.coeff 337 =
      -(((((2584947581926 * 10 ^ 70 +
        2582625123734056551677926253634530994012242229292428396061718138643725) * 10 ^ 70 +
        8114996883835852667237486285383374945745333638631136135854964923185515) * 10 ^ 70 +
        2932973208279986344313183377578199496704546472065483712355789071605783) * 10 ^ 70 +
        5941739726874469822473819472562156682465085735604042092283423973210444) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (337 - x)) = _
  rw [show 338 = 0 +
    338 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 338 = 32 +
      306 by norm_num, Finset.sum_range_add]
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
    rw [show 178 = 9 +
      169 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (338 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_338 :
    recurrence4Scalar2Second.coeff 338 =
      (((((1196568650862 * 10 ^ 70 +
        5900561863070254171061476623682973801857333145957309698375705505889891) * 10 ^ 70 +
        0158731546974460113201550292635215677634011271414786529375673628499250) * 10 ^ 70 +
        6451086638170848368141879696191207305855375020574439325972928244070291) * 10 ^ 70 +
        6012682891783013202768999490234036022590192719334146639471111861969672) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (338 - x)) = _
  rw [show 339 = 0 +
    339 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 339 = 32 +
      307 by norm_num, Finset.sum_range_add]
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
    rw [show 179 = 9 +
      170 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (339 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_339 :
    recurrence4Scalar2Second.coeff 339 =
      -(((((543351689906 * 10 ^ 70 +
        8538872901866257146720660521458580117469326438244102834327199325541358) * 10 ^ 70 +
        1226875175053064738059107214620301161928204807723377149894580846679447) * 10 ^ 70 +
        7122869513465079038175098237401965983586571989032619823130166004324963) * 10 ^ 70 +
        1590025655972753954200516639897351093364914957490930498437422852344092) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (339 - x)) = _
  rw [show 340 = 0 +
    340 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 340 = 32 +
      308 by norm_num, Finset.sum_range_add]
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
    rw [show 180 = 9 +
      171 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (340 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_340 :
    recurrence4Scalar2Second.coeff 340 =
      (((((242026273074 * 10 ^ 70 +
        3009798894316339677170195986593449759777812702914205845984154253956041) * 10 ^ 70 +
        1685380310258465177411509479197929609316543620689190388083072104001897) * 10 ^ 70 +
        3407968566081440467514013618699952552715905804422687526156575621675377) * 10 ^ 70 +
        7283456543970652986800828857955370032984778611163276082526398166836597) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (340 - x)) = _
  rw [show 341 = 0 +
    341 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 341 = 32 +
      309 by norm_num, Finset.sum_range_add]
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
    rw [show 181 = 9 +
      172 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (341 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_341 :
    recurrence4Scalar2Second.coeff 341 =
      -(((((105734237165 * 10 ^ 70 +
        4932104279047487310638241469366502979021122106536757370289532207259530) * 10 ^ 70 +
        9513854376337957955215593251883792232747955880081693536117336035610681) * 10 ^ 70 +
        4551070844230898079338344965082234361423302890264935450358017234688266) * 10 ^ 70 +
        9879314670433307177107504325919118902582120709542213959909686975712996) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (341 - x)) = _
  rw [show 342 = 0 +
    342 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 342 = 32 +
      310 by norm_num, Finset.sum_range_add]
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
    rw [show 182 = 9 +
      173 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (342 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_342 :
    recurrence4Scalar2Second.coeff 342 =
      (((((45293342915 * 10 ^ 70 +
        7489775298368620051075319712726131412309776985923125948355863673466763) * 10 ^ 70 +
        0913915087345498081336591625162490984265901932207994897465735030942417) * 10 ^ 70 +
        5054912503997468850441678358530566579967287989851890103156939602364150) * 10 ^ 70 +
        9274141736876094748613305319407641026120218439774986421961948587703720) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (342 - x)) = _
  rw [show 343 = 0 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 9 +
      174 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (343 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_343 :
    recurrence4Scalar2Second.coeff 343 =
      -(((((19018728839 * 10 ^ 70 +
        1728224512914311033458272709808048697688346478681894067479243582845166) * 10 ^ 70 +
        1922730900779946930328541134088896649226995170219416157901064878754765) * 10 ^ 70 +
        7962699913930496375975711248143138055363965349756472920743381672053987) * 10 ^ 70 +
        6970245011752527749769568804098978818692428067649354228885608594187683) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (343 - x)) = _
  rw [show 344 = 0 +
    344 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 344 = 32 +
      312 by norm_num, Finset.sum_range_add]
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
    rw [show 184 = 9 +
      175 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (344 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_344 :
    recurrence4Scalar2Second.coeff 344 =
      (((((7825280664 * 10 ^ 70 +
        3601927449185696390679806274090941033311609301201279849700888526898690) * 10 ^ 70 +
        8655231556114352027391178548269302392731592993022818757852300205608699) * 10 ^ 70 +
        5847367997912043903191648830523614123284858172838655823150610337044830) * 10 ^ 70 +
        0000384516725501317189722015883292579798822800023491855136876114363832) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (344 - x)) = _
  rw [show 345 = 0 +
    345 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 345 = 32 +
      313 by norm_num, Finset.sum_range_add]
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
    rw [show 185 = 9 +
      176 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (345 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_345 :
    recurrence4Scalar2Second.coeff 345 =
      -(((((3153775571 * 10 ^ 70 +
        5175018259208044073358800952617003476803299193388599938995936422084743) * 10 ^ 70 +
        1062124240439967398100574011579200647401941210496145521711013218244006) * 10 ^ 70 +
        9451988721880185813412702777976268725400210402421147171655459888103060) * 10 ^ 70 +
        9923589573339730291410359655493698270351501282275060437543311870848220) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (345 - x)) = _
  rw [show 346 = 0 +
    346 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 346 = 32 +
      314 by norm_num, Finset.sum_range_add]
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (346 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_346 :
    recurrence4Scalar2Second.coeff 346 =
      (((((1244638939 * 10 ^ 70 +
        8750968444097180972202644871257166464333978787052128469407151934660027) * 10 ^ 70 +
        6372730067928450979777923215580221110421567233508896149485108010148284) * 10 ^ 70 +
        6233899623429915100790013825950561274854338488386723571114300894450710) * 10 ^ 70 +
        2485138620493522517203332505231646022979010198605240453911003623610155) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (346 - x)) = _
  rw [show 347 = 0 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 9 +
      178 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (347 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_347 :
    recurrence4Scalar2Second.coeff 347 =
      -(((((480935323 * 10 ^ 70 +
        4933997523408705300402501450059027675152270987694590835502000190535247) * 10 ^ 70 +
        1810974227216773007819479178407334563030567176247510736198626359730646) * 10 ^ 70 +
        9938490698937705446173852904634316056357540605041571224657608648321272) * 10 ^ 70 +
        4785495004746658015391720857029202175412287719843591508891584669370362) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (347 - x)) = _
  rw [show 348 = 1 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 8 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (348 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_348 :
    recurrence4Scalar2Second.coeff 348 =
      (((((182002406 * 10 ^ 70 +
        1630168182907375094134900624430087626989327369610045012152752344074886) * 10 ^ 70 +
        9403239507436398376825994435314036295416875639782408611009690121588644) * 10 ^ 70 +
        3600327461243456088540846895836530478391740337774216498296770979802416) * 10 ^ 70 +
        8964888521776926176789275756765351224605585227693955653424383948354235) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (348 - x)) = _
  rw [show 349 = 2 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 7 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (349 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_349 :
    recurrence4Scalar2Second.coeff 349 =
      -(((((67522175 * 10 ^ 70 +
        6548553165996147796359318420241182642909162653012511439409975528428854) * 10 ^ 70 +
        3173439040820977356800628958931524092261658073173465749482455265224077) * 10 ^ 70 +
        2785543980651926621986154592519065717978591737074766143745273855800991) * 10 ^ 70 +
        5566800927337579014821243884690319683232259276949763257978817861764878) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (349 - x)) = _
  rw [show 350 = 3 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 6 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
