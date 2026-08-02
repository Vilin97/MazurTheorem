/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar2Second_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (217 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_217 :
    recurrence4Scalar2Second.coeff 217 =
      -(((((898347868518803073014500 * 10 ^ 70 +
        2546832504941276890535142544475411813484972618781760094506879929081838) * 10 ^ 70 +
        0581668792900033800749235122444873324179859166285919440468531081444544) * 10 ^ 70 +
        5439567096339355952653525194266805580124082121971402612460700348291246) * 10 ^ 70 +
        1780709927635232511036336761709174859636702683741547473136810323631617) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (217 - x)) = _
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 9 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (218 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_218 :
    recurrence4Scalar2Second.coeff 218 =
      (((((1385662994003916923652553 * 10 ^ 70 +
        0861716491857324266403708483120382727509450281121273240487643022954798) * 10 ^ 70 +
        1825748560538336065620305177173770243054483048243363912095804692768164) * 10 ^ 70 +
        8729123463520513904948545384459515188371850902979174463371459009104766) * 10 ^ 70 +
        7401896140733610320203360638134903717510104200920795841113887098589524) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (218 - x)) = _
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 9 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (219 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_219 :
    recurrence4Scalar2Second.coeff 219 =
      -(((((2104171747663455788219039 * 10 ^ 70 +
        1372839321062325235782756730401382885998708846825426636885465705559164) * 10 ^ 70 +
        5826204591841512090541999159580959183632556625725223527078825783833682) * 10 ^ 70 +
        3259649922238618566362527174773963493074773820474302963964444791267931) * 10 ^ 70 +
        8442579377370833727531014027311412826039303063439171706489493184954762) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (219 - x)) = _
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 9 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (220 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_220 :
    recurrence4Scalar2Second.coeff 220 =
      (((((3145137576081187258740481 * 10 ^ 70 +
        2027175747066700313892178028858054925547035819349064506752124321925353) * 10 ^ 70 +
        7749298244337162741978387739159021773519522176011496303954056039419616) * 10 ^ 70 +
        2334212702546438820789695644698967490953123061985957058177996880810185) * 10 ^ 70 +
        8421346184176174145342229674404976334946211051313273626680169609305123) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (220 - x)) = _
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 9 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (221 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_221 :
    recurrence4Scalar2Second.coeff 221 =
      -(((((4626429498476710055103821 * 10 ^ 70 +
        8796966160211058064075744729957166456677106433942041406814247875932942) * 10 ^ 70 +
        7604035185770626829783214978082752231875391374619796828539746629312026) * 10 ^ 70 +
        8586775864068231210820056370263356708108135176541342465572946164595130) * 10 ^ 70 +
        7852483515245315036029088165956096033391886228444603082249652194256721) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (221 - x)) = _
  rw [show 222 = 0 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 9 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (222 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_222 :
    recurrence4Scalar2Second.coeff 222 =
      (((((6695752004413467958766979 * 10 ^ 70 +
        1044349566296537220285761342490024091355842952145699735840956322188012) * 10 ^ 70 +
        4913613500704930455419318673755779044777527051416179865992787364362995) * 10 ^ 70 +
        0204086564631565300775091918716940252472944485134040934173405758564337) * 10 ^ 70 +
        7830421197565500040656456781056542166761711750821501451966406404589586) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (222 - x)) = _
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
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 9 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (223 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_223 :
    recurrence4Scalar2Second.coeff 223 =
      -(((((9531970490585233472022131 * 10 ^ 70 +
        6442977420606888227245867379339330873608752650177439123024196126050182) * 10 ^ 70 +
        1776913987857942529704307271026063773327166805319791729141223343516318) * 10 ^ 70 +
        1165136301092725586234372715432453021814771391982839624204021275610620) * 10 ^ 70 +
        7756229226165887953240921732511187560570733646451569959205430848328388) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (223 - x)) = _
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
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 9 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (224 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_224 :
    recurrence4Scalar2Second.coeff 224 =
      (((((13343160294238660504832867 * 10 ^ 70 +
        6363716529992335584246732320371866387724082277453599217818215121917901) * 10 ^ 70 +
        3619816394975664730768229711175059086458679745143137914693583634398070) * 10 ^ 70 +
        8519829863509302596285448020441131447469159162402251063421879246736030) * 10 ^ 70 +
        8545187437425863316515088725360451153707765140920459087901690212476431) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (224 - x)) = _
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
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 9 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (225 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_225 :
    recurrence4Scalar2Second.coeff 225 =
      -(((((18359696301951216206742413 * 10 ^ 70 +
        8879765655414398734774050662880525252446370592029735862203577094712039) * 10 ^ 70 +
        1277509087311848789460156440832738250648845350298524118113766570373962) * 10 ^ 70 +
        3632457405954549463420541685020188079422221219562570420607513688356623) * 10 ^ 70 +
        1240917268936149624984576294821496855509449325908592147799569388971679) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (225 - x)) = _
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
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 9 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (226 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_226 :
    recurrence4Scalar2Second.coeff 226 =
      (((((24820490995430949033246180 * 10 ^ 70 +
        5941264801036246400196473598561033793477230633049539817494100498573643) * 10 ^ 70 +
        2579869924690478239010575079432831552578557668973465549945492736148339) * 10 ^ 70 +
        9504572684983317185228506035644485554434048422019522149802762842759613) * 10 ^ 70 +
        8671433517033587629715787295469708887065424150062765355207869513515270) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (226 - x)) = _
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 9 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (227 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_227 :
    recurrence4Scalar2Second.coeff 227 =
      -(((((32950475981672660359788417 * 10 ^ 70 +
        8413482359870367296237655791041854069959255517621351617719571186339293) * 10 ^ 70 +
        3182880239169783869243053194850063566062175662702420564106548177789389) * 10 ^ 70 +
        0819118287048138638542028924647509660782914748103917032607983201756055) * 10 ^ 70 +
        1434661085740380464053461639573778966714366332030193985566242361936674) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (227 - x)) = _
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
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 9 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (228 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_228 :
    recurrence4Scalar2Second.coeff 228 =
      (((((42927712812496522253221437 * 10 ^ 70 +
        4041022748149003835228945578467063547993713435714476124447717390435520) * 10 ^ 70 +
        8274333628404181592042929293744271442063479145403331974336639876295029) * 10 ^ 70 +
        0825094380104940963600258514064958270695572836397237711040795153350398) * 10 ^ 70 +
        1542709523582967688249635371240514076837338072405532503572400677536240) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (228 - x)) = _
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
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 9 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (229 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_229 :
    recurrence4Scalar2Second.coeff 229 =
      -(((((54839217908201621896302436 * 10 ^ 70 +
        1102416926349572559710814991284177697563325386015480971088186926562291) * 10 ^ 70 +
        2158288354340999981732637692894505289178446408591815751362696579768774) * 10 ^ 70 +
        2784277767663425879467758481051501810809019156178917980874137584489527) * 10 ^ 70 +
        6081251521119379723469659446147726348216911856889759648768493704544406) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (229 - x)) = _
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
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 9 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (230 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_230 :
    recurrence4Scalar2Second.coeff 230 =
      (((((68625772822429545715140736 * 10 ^ 70 +
        7171471468335273004449587529674276427253200008109300913338494314220225) * 10 ^ 70 +
        7672920604813833695302009085185104878960288603769005098223150633854107) * 10 ^ 70 +
        5682855681295658528426610980746442807314706071021080939779768182816085) * 10 ^ 70 +
        1909515417024375283856006956332739790739449102508648714156553185413410) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (230 - x)) = _
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
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 9 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (231 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_231 :
    recurrence4Scalar2Second.coeff 231 =
      -(((((84017689912515009781305707 * 10 ^ 70 +
        4258834773614367441272021782954254172242688498995503266113064347357634) * 10 ^ 70 +
        3890070092296455013383197968855213136573587364615083643365447904432200) * 10 ^ 70 +
        6862019125418056868221832404878008867963429504743032242531594306987698) * 10 ^ 70 +
        2715410444194716550944457503362632754652987840564445898199098314342134) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (231 - x)) = _
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
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 9 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (232 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_232 :
    recurrence4Scalar2Second.coeff 232 =
      (((((100465655123681960789367887 * 10 ^ 70 +
        9934556175899312919684083554858486024920400347598281307425417455870844) * 10 ^ 70 +
        0520753203393327688817398134926167374040319143447843201732465140934175) * 10 ^ 70 +
        0026796796837549557767189484289532349161239763747359415676151149534360) * 10 ^ 70 +
        6837318515504249651508113338094716880348572308028254968827212181733304) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (232 - x)) = _
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
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 9 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (233 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_233 :
    recurrence4Scalar2Second.coeff 233 =
      -(((((117073203975932261849607332 * 10 ^ 70 +
        8422645163874847496680410383754830479803254240824996411739198368099296) * 10 ^ 70 +
        0303611881293885047041776442550069080012627745534092229050609783028965) * 10 ^ 70 +
        9998165496240275671859319754553050723213458924478186876709853591162682) * 10 ^ 70 +
        4756809813739036291405588603906104799214335944783173868480077160432769) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (233 - x)) = _
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
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 9 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (234 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_234 :
    recurrence4Scalar2Second.coeff 234 =
      (((((132539809960375403997456798 * 10 ^ 70 +
        4273426421020469745519464366143451254886406563005728107227383068912211) * 10 ^ 70 +
        5131848608472775098499174092234457295025978841954127771234198090584426) * 10 ^ 70 +
        4407881891871658777924335825127434941316226810183897369195801303314442) * 10 ^ 70 +
        2080781706586247138274012587126278068658623249139844902639172277204425) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (234 - x)) = _
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
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 9 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (235 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_235 :
    recurrence4Scalar2Second.coeff 235 =
      -(((((145125565947528555077070026 * 10 ^ 70 +
        0068866350150436674421205815296084740602512860016751541468396501634929) * 10 ^ 70 +
        5872913855535195673792545012252626987288918374534251789816126984006816) * 10 ^ 70 +
        0925512128027101115885113077585310099764323228452867633526076797883525) * 10 ^ 70 +
        8127022067822646506041346857031303063200691641687487177188441571513630) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (235 - x)) = _
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
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 9 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (236 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_236 :
    recurrence4Scalar2Second.coeff 236 =
      (((((152649527116381706552789905 * 10 ^ 70 +
        2068733478572527766667055952638939252779348248185686189032141959054614) * 10 ^ 70 +
        2642187604623392272219647424195150389319163096976012206539178829116542) * 10 ^ 70 +
        6195756421265731746942522294001953324762398388736785763505800847432454) * 10 ^ 70 +
        5313707808635318550550443100293477256593200276227710626515461202314211) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (236 - x)) = _
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
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 9 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (237 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_237 :
    recurrence4Scalar2Second.coeff 237 =
      -(((((152533450935891103320964454 * 10 ^ 70 +
        0384699790798476596669357381243048869214999214536018361344902273586031) * 10 ^ 70 +
        2569073061801728842008483798337623075099377131938313287325952828781318) * 10 ^ 70 +
        7686966227505585531524104147585302671007125843363154594390601576821435) * 10 ^ 70 +
        5976512721714654427443202863795616121586081454272734408760391720829023) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (237 - x)) = _
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
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 9 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (238 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_238 :
    recurrence4Scalar2Second.coeff 238 =
      (((((141900485655519552664965681 * 10 ^ 70 +
        0583987535045589109599534235052511004295989945609360128089916067328857) * 10 ^ 70 +
        8804660720683058582455556869076131124832026737467581329241319968606335) * 10 ^ 70 +
        1023876944410981176777324849117495045666778428455770570553608655684982) * 10 ^ 70 +
        6279711775173886646688008218801709675571561710677866794204516491188155) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (238 - x)) = _
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
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 9 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (239 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_239 :
    recurrence4Scalar2Second.coeff 239 =
      -(((((117734079399049177659333315 * 10 ^ 70 +
        2491266122851303771184532361498961734879467738234061019498311359361915) * 10 ^ 70 +
        3017479682894132440671487574171973082155557142536974373288248085985360) * 10 ^ 70 +
        1756417068503565294755484263373687081295872000149862337310821472471517) * 10 ^ 70 +
        0291927534941055565264596367457806307547944870347659645716301257797923) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (239 - x)) = _
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
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 9 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (240 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_240 :
    recurrence4Scalar2Second.coeff 240 =
      (((((77096055346362783712103612 * 10 ^ 70 +
        4773272635724986758905036717479128922853170388160746761431980259574936) * 10 ^ 70 +
        9795165989537087273762809139611341160166859057880902882163477013423552) * 10 ^ 70 +
        7204154376970963491570982883541751186115690512936230266023958476981788) * 10 ^ 70 +
        7859101739968822970722195323318499290765751609913502676193400489167264) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (240 - x)) = _
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
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 9 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (241 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_241 :
    recurrence4Scalar2Second.coeff 241 =
      -(((((17394844308470260331724164 * 10 ^ 70 +
        8265723011706243502422601808345546344431731601174767110115356396228294) * 10 ^ 70 +
        9537888432747970446576487758568966671486839456571633348172631836863139) * 10 ^ 70 +
        8413743392896193697939074196302862013560320675753996099219683893524314) * 10 ^ 70 +
        3471022733022214029012761323301460380446894100651628573495975250475446) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (241 - x)) = _
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
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 9 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (242 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_242 :
    recurrence4Scalar2Second.coeff 242 =
      -(((((63313897206107209041451620 * 10 ^ 70 +
        3334759641962509538851333054533647945568580565823075542789092894293757) * 10 ^ 70 +
        9716630282236244858905644722106692101312533729772557347591188028020297) * 10 ^ 70 +
        1950888962128881338009316133088631726400803975505116134699268239902374) * 10 ^ 70 +
        6814260923963390563029613436710730984791827049169673098192230195298627) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (242 - x)) = _
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (243 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_243 :
    recurrence4Scalar2Second.coeff 243 =
      (((((166020455846232333676605871 * 10 ^ 70 +
        5081900227612218433018095744954691241156269091408801994097757902760339) * 10 ^ 70 +
        6066896778671247820732158749671843348207995588679239056674323363159494) * 10 ^ 70 +
        4972810917531703194285899222969921170434134136639998550419173285571253) * 10 ^ 70 +
        3457686010101896628246216528501635844615458798639878944729734657751768) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (243 - x)) = _
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
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 9 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (244 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_244 :
    recurrence4Scalar2Second.coeff 244 =
      -(((((290480830804459480945177706 * 10 ^ 70 +
        1679346845719439212256651613538876409940863691425261210358102707436272) * 10 ^ 70 +
        4448555188901957397335469099326816449649069789179214801500148928803434) * 10 ^ 70 +
        1979109193244092962348342335814913452752714254281790923348175325192324) * 10 ^ 70 +
        9360489831026473152966642799449650540074353078246047812546870729692263) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (244 - x)) = _
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
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 9 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (245 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_245 :
    recurrence4Scalar2Second.coeff 245 =
      (((((434999381976932099151541258 * 10 ^ 70 +
        0593997680892914799664878554337101759717497627209696594559340797902338) * 10 ^ 70 +
        6886102036896952252365895933136805952017456734724833600809037001487615) * 10 ^ 70 +
        2007011484949108111657586312054671242070047247127685494176533176264391) * 10 ^ 70 +
        6904172866098410733329650661677535710130985325786716725649248471272392) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (245 - x)) = _
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
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 9 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (246 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_246 :
    recurrence4Scalar2Second.coeff 246 =
      -(((((596309740078717068084273635 * 10 ^ 70 +
        3951717016470297869848372476821420512564451964585397888473225445940868) * 10 ^ 70 +
        2297278110241762447569095777594693056966749701507605442033092597877974) * 10 ^ 70 +
        7678140377456723044963789831028526937565581284663798283250800239079568) * 10 ^ 70 +
        7269698062065271711713944717848832626915859934648420110829941553493992) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (246 - x)) = _
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
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 9 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (247 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_247 :
    recurrence4Scalar2Second.coeff 247 =
      (((((769583420800223511262768168 * 10 ^ 70 +
        6008840419450882197559814715005745264060673611193553331076451040293406) * 10 ^ 70 +
        0314314105671109707314948613576431136811243256562074992689241471172693) * 10 ^ 70 +
        6417655775417550223122693021940398602685367025990563762131696666265602) * 10 ^ 70 +
        7902365788259363338296976044238635060764779089369735696398268405879354) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (247 - x)) = _
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
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 9 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (248 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_248 :
    recurrence4Scalar2Second.coeff 248 =
      -(((((948584625598239398509913012 * 10 ^ 70 +
        7392538295698692990654425938067225885143466620669090692722430984458872) * 10 ^ 70 +
        6768551068814079594177878478585956007014483788245771921277228198324621) * 10 ^ 70 +
        8999078527857957319087330745010376204368607035618351853251486287211002) * 10 ^ 70 +
        5187178228828434311877219198239320580554268535899247924941364304536452) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (248 - x)) = _
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
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 9 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (249 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_249 :
    recurrence4Scalar2Second.coeff 249 =
      (((((1125974593519099614233541666 * 10 ^ 70 +
        2278616896075037626173804052402508118719270333459568761192378113008817) * 10 ^ 70 +
        3170012394482966723802124184689617006742633775843391606212817274561761) * 10 ^ 70 +
        7815828663331646584715829365666116837616456062715769531306505110654297) * 10 ^ 70 +
        1819403847657647250632352210752405744859031990910362636974067440626224) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (249 - x)) = _
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
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 9 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (250 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_250 :
    recurrence4Scalar2Second.coeff 250 =
      -(((((1293751260788872420216882193 * 10 ^ 70 +
        6530050065336562826339082317488904615793990745440397805124067474557157) * 10 ^ 70 +
        0692948239765816136309412307512158147461048909356089191517642787201735) * 10 ^ 70 +
        6079920528452422651338088475856340894394416259086434692359129014131147) * 10 ^ 70 +
        7299840119080854428913536330118394918215802429776599343788624389806313) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (250 - x)) = _
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
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 9 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (251 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_251 :
    recurrence4Scalar2Second.coeff 251 =
      (((((1443792186039145153901749298 * 10 ^ 70 +
        1642826614663998455493556620608718603889271365292278611519095375825178) * 10 ^ 70 +
        6565238321307304100331225945755243976130454090745474784988438061304820) * 10 ^ 70 +
        5974155709497861404667590969594105238078574508217778674165932537887553) * 10 ^ 70 +
        5345289746642570405521431208262327261635369491297493370687833917881580) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (251 - x)) = _
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
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 9 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (252 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_252 :
    recurrence4Scalar2Second.coeff 252 =
      -(((((1568453312105850328390915928 * 10 ^ 70 +
        8757976170559150169324260860598238173873859422847343465470614863062165) * 10 ^ 70 +
        7926438090726304493830193760550641687720392192809050824069289451049480) * 10 ^ 70 +
        9864663520620649525730228194670839966015668439946248180850335871141912) * 10 ^ 70 +
        4603464782949445670571155360773681626538029509651401391532579131791629) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (252 - x)) = _
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
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 9 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (253 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_253 :
    recurrence4Scalar2Second.coeff 253 =
      (((((1661165647990363939937008065 * 10 ^ 70 +
        2923723255290435618076582941409337667595642841395772624648344745011836) * 10 ^ 70 +
        8529772222289974735516809012154901859524837404903373314673451332512285) * 10 ^ 70 +
        6338782176278388270574587564346002872474777056314971839395384829978388) * 10 ^ 70 +
        1159181524530408580009300934611729153309432788381248781470469728591800) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (253 - x)) = _
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
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 9 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (254 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_254 :
    recurrence4Scalar2Second.coeff 254 =
      -(((((1716968296175243830668618467 * 10 ^ 70 +
        0286640286342367818011551306810484862268276312737217520914680952722403) * 10 ^ 70 +
        9666954262887528284049577536135788403452836373847093486596288829775126) * 10 ^ 70 +
        8535426818404721781521583391819625463714633019551485652184496478968266) * 10 ^ 70 +
        2354850075439523806471664037820078319425109643226895315668319295993829) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (254 - x)) = _
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
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 9 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (255 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_255 :
    recurrence4Scalar2Second.coeff 255 =
      (((((1732920413287398286266609754 * 10 ^ 70 +
        1327994549115458041495148324970423989262912152120080306797123136803482) * 10 ^ 70 +
        0271093711685760756218099354947650201985202338044299620213445615611439) * 10 ^ 70 +
        6832682418163508716974722078795488556875041428819875681066873702592962) * 10 ^ 70 +
        3434288011047150684921517839070027892688347862980559036285065446919618) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (255 - x)) = _
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
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 9 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (256 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_256 :
    recurrence4Scalar2Second.coeff 256 =
      -(((((1708346496969869761431297238 * 10 ^ 70 +
        8241498523992013142105309867898249633603298787890991222357097913209628) * 10 ^ 70 +
        4634878228353878817342380904739565005150149747163135578058120743827784) * 10 ^ 70 +
        8423878697952008919877608429530651719816468317444916416484958744394312) * 10 ^ 70 +
        2208517682432398221676713197192867520811291827832210352771281970845818) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (256 - x)) = _
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
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 9 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (257 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_257 :
    recurrence4Scalar2Second.coeff 257 =
      (((((1644887454909533140452847969 * 10 ^ 70 +
        6413676651152469252798103176017472639962897478931598206477133732327175) * 10 ^ 70 +
        2928955383656469692400931817512995653743130292862482199288996060716146) * 10 ^ 70 +
        6626135996583633913929415852280866042942177788374674135510229228577055) * 10 ^ 70 +
        2561245963848492755823074433911789558614118941802263649202916565343612) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (257 - x)) = _
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
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 9 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (258 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_258 :
    recurrence4Scalar2Second.coeff 258 =
      -(((((1546351829959106466478821213 * 10 ^ 70 +
        5114736390367526503935432549443570522691625393596855003478936744542528) * 10 ^ 70 +
        1874026094276530613223037946954901542870881520471365202812778057188242) * 10 ^ 70 +
        4329513180253008644738718368288078145905370613799061937959263060677580) * 10 ^ 70 +
        0967083885852469581357398042466073590213780338618285205929655706269837) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (258 - x)) = _
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
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 9 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (259 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_259 :
    recurrence4Scalar2Second.coeff 259 =
      (((((1418384282241222260374349369 * 10 ^ 70 +
        1943230517132771813172849812863054360923107469508642360750796904841697) * 10 ^ 70 +
        0827705918325918411823167337130920708100905820329127928298004268662385) * 10 ^ 70 +
        4831405931096851353985041794233272793480256881597977131811969789722367) * 10 ^ 70 +
        7164372440505090707341198486611315163803049373639914416399669608368963) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (259 - x)) = _
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
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 9 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (260 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_260 :
    recurrence4Scalar2Second.coeff 260 =
      -(((((1267988777132831172449674944 * 10 ^ 70 +
        8692961897802132260152964029771442158124845154394548716294581013921679) * 10 ^ 70 +
        0429582028010903236156487668245110835775085483921327265788764208452951) * 10 ^ 70 +
        0897042725421397667953143978644413033105306558709224426683691778488350) * 10 ^ 70 +
        5750382358239314520503036559570046585563764146115047353369799710845212) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (260 - x)) = _
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
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 9 +
      92 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (261 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_261 :
    recurrence4Scalar2Second.coeff 261 =
      (((((1102959097058281122069150795 * 10 ^ 70 +
        5455371553277452374673568006358510373587404646710888962564211866878499) * 10 ^ 70 +
        2132024116757600111472529307601705069556535412803573104633435543260823) * 10 ^ 70 +
        0949266063732364117006549942379745350146629689848344869795554925841387) * 10 ^ 70 +
        6382035345827136700723563279077829753382244311906833313293739737545291) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (261 - x)) = _
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
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 9 +
      93 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (262 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_262 :
    recurrence4Scalar2Second.coeff 262 =
      -(((((931277330288171622912019006 * 10 ^ 70 +
        1967854856560142683434131807260765944806660951249377603991411089813546) * 10 ^ 70 +
        0479248339419425419098627379264404067991990210526712323593149684613158) * 10 ^ 70 +
        8243306205239279610852214499446486483717226040938554372348585301860024) * 10 ^ 70 +
        8258713140313228681746121310495054414996059656767348799556081131195168) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (262 - x)) = _
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
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 9 +
      94 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (263 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_263 :
    recurrence4Scalar2Second.coeff 263 =
      (((((760541080613346795191862605 * 10 ^ 70 +
        7073429239835332227029676111428896265937878461284745720102601805160854) * 10 ^ 70 +
        5064948404481842852701377312079954445760755269040111284140153431225482) * 10 ^ 70 +
        7541627467130310372044042423083706445420028792947055961173639782222759) * 10 ^ 70 +
        1623620710539232993340866235804380598635916846942042058055370650365752) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (263 - x)) = _
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
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 9 +
      95 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (264 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_264 :
    recurrence4Scalar2Second.coeff 264 =
      -(((((597472708247776478353057170 * 10 ^ 70 +
        7654606943071238109635447495723828278683869270036862203157651109481692) * 10 ^ 70 +
        4915309443732969561412882887104621708126021666848380631898091255921350) * 10 ^ 70 +
        3930823940717148639119679022880084920326448543307309927894325161229239) * 10 ^ 70 +
        0443619590841716388450008328124257934515363927283461495352978822695150) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (264 - x)) = _
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
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 9 +
      96 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (265 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_265 :
    recurrence4Scalar2Second.coeff 265 =
      (((((447550473670227238263660913 * 10 ^ 70 +
        7780431212478658245356504310017083170492306760205949069383115848972421) * 10 ^ 70 +
        5322746373816541425658184368666720034286352770501614074929898674430252) * 10 ^ 70 +
        6746216143579392693443181853331986938756086109425100481100753481945018) * 10 ^ 70 +
        2650323534001144217278730626601607472062670422756416977930141363038582) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (265 - x)) = _
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 9 +
      97 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (266 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_266 :
    recurrence4Scalar2Second.coeff 266 =
      -(((((314784313456937445212466038 * 10 ^ 70 +
        7681293856997151689519273813884324480149818884689527872639499002612240) * 10 ^ 70 +
        1205044391787234414775609156342038207000891410594998386530094076603558) * 10 ^ 70 +
        6742962029289420881700346797532669135779235741009712225447781008506301) * 10 ^ 70 +
        1972271912667198338826675615692936903452050546777684440873975810837701) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (266 - x)) = _
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
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 9 +
      98 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (267 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_267 :
    recurrence4Scalar2Second.coeff 267 =
      (((((201640783580780987586926897 * 10 ^ 70 +
        0120996859328443127320285264792328154462379511548541949456680179133505) * 10 ^ 70 +
        3130050798057809649183391608149990382613093996444391383025408673669052) * 10 ^ 70 +
        9779113552762253485910618748368999675150418600813183666307826601674154) * 10 ^ 70 +
        1391508427332640129504412556081172887770673668206199265145124474082397) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (267 - x)) = _
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
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 9 +
      99 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (268 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_268 :
    recurrence4Scalar2Second.coeff 268 =
      -(((((109105010876330802145974578 * 10 ^ 70 +
        9561674527559812469549161949852226482495589139192044405201138789675473) * 10 ^ 70 +
        1160005021641124159451239359873643122758028588012572339545313293806555) * 10 ^ 70 +
        8493176533658290172006124935281755916213852543091827907235705242512999) * 10 ^ 70 +
        6395613610941479459256240514932559959057740588361347845625006990603410) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (268 - x)) = _
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
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 9 +
      100 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (269 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_269 :
    recurrence4Scalar2Second.coeff 269 =
      (((((36854349200274361248162063 * 10 ^ 70 +
        7227830894178320360812159387083181011940909508055264856877606345145320) * 10 ^ 70 +
        4517831650825608053272571200794170296861233469782453239555644442674622) * 10 ^ 70 +
        0527689977388736037242807361277313811571475454519189820872997532390285) * 10 ^ 70 +
        2777917621136458887437580987975058007731805589801370390629017590745305) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (269 - x)) = _
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
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 9 +
      101 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (270 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_270 :
    recurrence4Scalar2Second.coeff 270 =
      (((((16489870340346019429828284 * 10 ^ 70 +
        0313955444727064457094154618668115033563658230428358889037881538466634) * 10 ^ 70 +
        2284861954228682924587672131266253987129696126206108802692144718784313) * 10 ^ 70 +
        8329561087193839788230664077492446147712569292182105380982074928867497) * 10 ^ 70 +
        9422732453299936768210665316528239119347402297432202118338970238277330) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (270 - x)) = _
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
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 9 +
      102 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (271 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_271 :
    recurrence4Scalar2Second.coeff 271 =
      -(((((53069160698828000098109566 * 10 ^ 70 +
        1627313786254244614661375384940648128973724231760754056876946171397148) * 10 ^ 70 +
        8187507311566243793911333063256933436192973369959438257086113859701780) * 10 ^ 70 +
        5877241860482126269613646262173370014135661110879299310290390559029200) * 10 ^ 70 +
        1824236565173321119686448887084759692521647643581973554368077471104720) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (271 - x)) = _
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
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 9 +
      103 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (272 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_272 :
    recurrence4Scalar2Second.coeff 272 =
      (((((75488141165473910516084959 * 10 ^ 70 +
        7939169718118875518680378579749136360563990114679043252860733671446675) * 10 ^ 70 +
        2759786203565073761804240567368717945629359972394466342379712824892411) * 10 ^ 70 +
        3941313760113272620444062942193223773105581044347007637204445925336627) * 10 ^ 70 +
        0914210030989351927938919958714028804814419688384677794096173263693070) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (272 - x)) = _
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
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 9 +
      104 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (273 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_273 :
    recurrence4Scalar2Second.coeff 273 =
      -(((((86537495581908543741132524 * 10 ^ 70 +
        0774610950640295215772719110924716645330790157809661330308512296479584) * 10 ^ 70 +
        0336648083777941942732034139466072513908245487543359960981448098595114) * 10 ^ 70 +
        8625531271106905255937215018541390951231550060074393918844473229988878) * 10 ^ 70 +
        9982826426038526107990529271153512999857133878063896349321007685533113) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (273 - x)) = _
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
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 9 +
      105 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (274 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_274 :
    recurrence4Scalar2Second.coeff 274 =
      (((((88960851900799647346967766 * 10 ^ 70 +
        1837208313871734665526971651439388318729163597512358763710408063354915) * 10 ^ 70 +
        3171527327306831077846744862989031061652087596909605802915210198263361) * 10 ^ 70 +
        1067869679772032206597915924618901776836247612124888428607888471250102) * 10 ^ 70 +
        4435119785812559758017093211327409405200883402358526198309011691575071) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (274 - x)) = _
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
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 9 +
      106 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (275 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_275 :
    recurrence4Scalar2Second.coeff 275 =
      -(((((85277857313716970694350832 * 10 ^ 70 +
        7783920172916966092399898267322420964234438903566378794528038793620457) * 10 ^ 70 +
        6942861233422743670114268504348715535640761403186978609303524909707520) * 10 ^ 70 +
        0582943014024242066050182436646887742652390159669135398513992175566024) * 10 ^ 70 +
        2484163885341427536819291648850147556179933981397377375150137869782534) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (275 - x)) = _
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
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 9 +
      107 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (276 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_276 :
    recurrence4Scalar2Second.coeff 276 =
      (((((77667188639151540276887471 * 10 ^ 70 +
        6239403352893988946823772949070636857197407585746999672286638508321806) * 10 ^ 70 +
        4193548142917499707253675675382458150895713775648383446142683232733999) * 10 ^ 70 +
        5433230372793292876848125172123692064721239291399691344015931199062034) * 10 ^ 70 +
        1649856065542487933600672667256153518774103924365904577302155421854798) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (276 - x)) = _
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
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 9 +
      108 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (277 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_277 :
    recurrence4Scalar2Second.coeff 277 =
      -(((((67906128905467586892031824 * 10 ^ 70 +
        3430764137939898222089144440264178522643843101839868913377410455060469) * 10 ^ 70 +
        6687160791529848213592631879193518474489999081474002116519144122647338) * 10 ^ 70 +
        8763286033778997335648037575168355454746033531485452024027177647735844) * 10 ^ 70 +
        4313879732452941780850544780977012321389005276659371032006030759468844) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (277 - x)) = _
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
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 9 +
      109 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (278 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_278 :
    recurrence4Scalar2Second.coeff 278 =
      (((((57358252551479175399810352 * 10 ^ 70 +
        7659934234818675452256934539955210676529021336770767068567627499506990) * 10 ^ 70 +
        8068916426414430456876157392616212018902992693501645492850806811211357) * 10 ^ 70 +
        9884153952595352046706625349321898274659816156471556280417102412070360) * 10 ^ 70 +
        7179544973700541460035798617898827091464775611137144383484158284952231) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (278 - x)) = _
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
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 9 +
      110 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (279 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_279 :
    recurrence4Scalar2Second.coeff 279 =
      -(((((46997873234482971147199352 * 10 ^ 70 +
        2267565716973528463807885548565196967479044725402622861925987583002704) * 10 ^ 70 +
        7789327112817393652587193620146422215521665912313470234060624288129638) * 10 ^ 70 +
        3909331192158873813947215833160747880888197204742332550085714829954033) * 10 ^ 70 +
        4703139447927124052574642727717417554152934026780065047584840898808451) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (279 - x)) = _
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
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 9 +
      111 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (280 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_280 :
    recurrence4Scalar2Second.coeff 280 =
      (((((37459052356999446209658312 * 10 ^ 70 +
        9521085921680512325646591017043849497644217943811812035291415511560304) * 10 ^ 70 +
        8384899411998360562287947521869105231698472829035798259300916679773478) * 10 ^ 70 +
        7390724940990801722014464748644070743089915213225010745083304927905873) * 10 ^ 70 +
        3367724049664963348142576359411467822538458200468008644005521684399324) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (280 - x)) = _
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
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 9 +
      112 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (281 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_281 :
    recurrence4Scalar2Second.coeff 281 =
      -(((((29097736047308866738796986 * 10 ^ 70 +
        4423510386425105090662944307182793761756598169752362695048653605414830) * 10 ^ 70 +
        0093063272452452637578414975404935946888756481806963392284057215228411) * 10 ^ 70 +
        3369880164259946461746477749327524407338447146352526911915654947619747) * 10 ^ 70 +
        2389515032399602679734767762321579431177556666535558915830913014778060) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (281 - x)) = _
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
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 9 +
      113 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (282 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_282 :
    recurrence4Scalar2Second.coeff 282 =
      (((((22057457163908352751128963 * 10 ^ 70 +
        7428119545683518188534861207159766136558645466226410424785497436533691) * 10 ^ 70 +
        8998125126998997410086020834690663311394648166173440265756444887617287) * 10 ^ 70 +
        8040126482431218784019808169959727647706858859557388320330280654377033) * 10 ^ 70 +
        1148412761516891838936071396527856526117724546501695459903200379337904) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (282 - x)) = _
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
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 9 +
      114 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (283 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_283 :
    recurrence4Scalar2Second.coeff 283 =
      -(((((16331470463644949804382075 * 10 ^ 70 +
        4378594592502235663233417603114055074198008435187430373433631551774051) * 10 ^ 70 +
        9409950363936700240037409285160403754808826178481574161414023367688065) * 10 ^ 70 +
        3084538293035623829036767869082103450895759367827186283881296212846574) * 10 ^ 70 +
        3952237979658047924465053346290068011242126874518374341708341284560543) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (283 - x)) = _
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
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 9 +
      115 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (284 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_284 :
    recurrence4Scalar2Second.coeff 284 =
      (((((11816718780104055397750621 * 10 ^ 70 +
        2215284905048602522519817349836950465900758332316130022777480554220466) * 10 ^ 70 +
        5496111955242173949123557574951815864143180430306565428840534887913501) * 10 ^ 70 +
        2762037366935133984329549149017238469215556220032957583489297566085104) * 10 ^ 70 +
        1753564321630164061687512737638680278156998073097250380221640834201684) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (284 - x)) = _
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
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 9 +
      116 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (285 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_285 :
    recurrence4Scalar2Second.coeff 285 =
      -(((((8357311477264559507536619 * 10 ^ 70 +
        8085842044679746263130910942405942464676480347665046042818272551614060) * 10 ^ 70 +
        5729345924883307870481618821096329262270149856159676264039494214995468) * 10 ^ 70 +
        0920993836512991754696075573044518676306765805991963964413265145244288) * 10 ^ 70 +
        6943325694742241014085721363076639753500093338398702648331704259276886) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (285 - x)) = _
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
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 9 +
      117 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (286 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_286 :
    recurrence4Scalar2Second.coeff 286 =
      (((((5777024979792683786996840 * 10 ^ 70 +
        8341822338789801408531607808609487809945899024031831294054032581501713) * 10 ^ 70 +
        1140293685442653437624616546131239193594869641874100730781194589279810) * 10 ^ 70 +
        0726326304514714657603709603793745995643135587710233423283870869197161) * 10 ^ 70 +
        8058492907829907029195441280998626080558217451230981768977708384122954) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (286 - x)) = _
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
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 9 +
      118 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (287 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_287 :
    recurrence4Scalar2Second.coeff 287 =
      -(((((3901625788929422785708430 * 10 ^ 70 +
        9871460230127811318667541521382033951815428574469239290013901733041142) * 10 ^ 70 +
        8858188520565085916068898155798586681611787473024915072770537445128038) * 10 ^ 70 +
        8807760250486719124792779848779690462910778048030945249942243564649230) * 10 ^ 70 +
        8403397526454283599185706731311148776008706956912572507557742248052512) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (287 - x)) = _
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
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 9 +
      119 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (288 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_288 :
    recurrence4Scalar2Second.coeff 288 =
      (((((2572584740032994783420144 * 10 ^ 70 +
        7069135125671584291159824884402504331968215484150141449082436866021519) * 10 ^ 70 +
        6318825793878364605632523296315963055450943997829967575289488001995518) * 10 ^ 70 +
        2812590086537178311684751860958542687542045997498368230926482587069573) * 10 ^ 70 +
        2894437794001134525989105251916561025399774286890919674314910062428284) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (288 - x)) = _
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
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 9 +
      120 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (289 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_289 :
    recurrence4Scalar2Second.coeff 289 =
      -(((((1654077886814268199215519 * 10 ^ 70 +
        7357064173691169804735277033306180221487065275535963111858838922032792) * 10 ^ 70 +
        4777266890543630900610574108305712363452219006932918712260982063088102) * 10 ^ 70 +
        4673763451891011574273264576712095459024577717820977633849385308322613) * 10 ^ 70 +
        2499935844076022784162099601771147638391547320614083608084774901357075) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (289 - x)) = _
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
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 9 +
      121 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (290 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_290 :
    recurrence4Scalar2Second.coeff 290 =
      (((((1035166713169483229641722 * 10 ^ 70 +
        9566883698982914918120987634691947462699603684562766799154345842102166) * 10 ^ 70 +
        3239971501537199067086586290746193861807376572714345691059549301172839) * 10 ^ 70 +
        7199429833864463927737738196627692046832970188730686982059921175955620) * 10 ^ 70 +
        2979068093035620402309725105538100674291671484376884713208418958847278) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (290 - x)) = _
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
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 9 +
      122 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (291 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_291 :
    recurrence4Scalar2Second.coeff 291 =
      -(((((628835660340593324940700 * 10 ^ 70 +
        2340477987530405495326717226279024634621916596842630292667660207510235) * 10 ^ 70 +
        5237057863705594713177290823804666412741746180930633313880269704030712) * 10 ^ 70 +
        4865900615546676824994816729196752883288722829662704252104436523432696) * 10 ^ 70 +
        9801402125272601939762649194260759947750770764597956698988923191437175) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (291 - x)) = _
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
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 9 +
      123 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (292 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_292 :
    recurrence4Scalar2Second.coeff 292 =
      (((((369241856909520522125162 * 10 ^ 70 +
        0246994555411044575710085437352189911989212119121644810595007450975508) * 10 ^ 70 +
        7168060654646214333145917728262327694448961267265255067254769564694155) * 10 ^ 70 +
        4199550072635012939634432703133616283742772287352672326870951653653020) * 10 ^ 70 +
        0034184811674422934688870989259128350155555710468893003532350727665186) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (292 - x)) = _
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
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 9 +
      124 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (293 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_293 :
    recurrence4Scalar2Second.coeff 293 =
      -(((((208180525217225902311858 * 10 ^ 70 +
        5381457507885641517323607440073973195068099664303061958388329999405944) * 10 ^ 70 +
        8617243013990294784201029777978366482998231599538142017337479918494400) * 10 ^ 70 +
        9686477997313102739185262968750239483775893384280877954426416283989266) * 10 ^ 70 +
        0753704506033921382489939238009945688183830955128272326388011095429439) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (293 - x)) = _
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
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 9 +
      125 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (294 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_294 :
    recurrence4Scalar2Second.coeff 294 =
      (((((111443570682608441179761 * 10 ^ 70 +
        7321241455642159802576239127385400086217356753480404396175484856065318) * 10 ^ 70 +
        2926558524445643997169662501295577023613891874190348750745154632922535) * 10 ^ 70 +
        7769213267338625018001132203147852426102881744681781453663005654363795) * 10 ^ 70 +
        0532784465385470421512727867026605998803650078607938610415568527308417) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (294 - x)) = _
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
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 9 +
      126 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (295 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_295 :
    recurrence4Scalar2Second.coeff 295 =
      -(((((55478068963052920805296 * 10 ^ 70 +
        7974536128333669816476693812875434526852100795826437310315493954777646) * 10 ^ 70 +
        5304912825667876215725649935456402192850654216581741960921461588194018) * 10 ^ 70 +
        9317193817134358999523899271183137871627263313214389594557096932792922) * 10 ^ 70 +
        1457531623312928169440857302175843055592505989650324332886400799779230) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (295 - x)) = _
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
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 9 +
      127 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (296 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_296 :
    recurrence4Scalar2Second.coeff 296 =
      (((((24546514872211444919339 * 10 ^ 70 +
        5066457994125686334547060425684581205413261735774071310944654370991239) * 10 ^ 70 +
        6920811900657184632771827746138389482257800447974667651164988467413185) * 10 ^ 70 +
        4510897266304189604609536658344343863362989013741326322935793396847489) * 10 ^ 70 +
        2377296891433844536236375361357576618062358250062123513001394184425304) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (296 - x)) = _
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
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 9 +
      128 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (297 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_297 :
    recurrence4Scalar2Second.coeff 297 =
      -(((((8449560885653012815484 * 10 ^ 70 +
        0441529219880176232063077822688728601094094612357381117033088965331912) * 10 ^ 70 +
        4030594965017654786308515038404643889542820373174593753051630881692401) * 10 ^ 70 +
        1120962492488179697847370773199770913875250917302717748460475435742148) * 10 ^ 70 +
        6170045490795188600537362742951923391080698819035576170134709869220138) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (297 - x)) = _
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 9 +
      129 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (298 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_298 :
    recurrence4Scalar2Second.coeff 298 =
      (((((784898976550181021266 * 10 ^ 70 +
        4766711978533553495853338708562182673789017883238290452353780426172497) * 10 ^ 70 +
        1672676559925854024237352107517051161360635724998361997225302917444665) * 10 ^ 70 +
        4057184051256524484053238879795101288586576721943555477795944527302580) * 10 ^ 70 +
        9438283014508572678289182692861616535911528051209241100700800904854374) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (298 - x)) = _
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
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 9 +
      130 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (299 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_299 :
    recurrence4Scalar2Second.coeff 299 =
      (((((2329729815238147931353 * 10 ^ 70 +
        1407506080725104113298074479076403117182860123693836711542880560224493) * 10 ^ 70 +
        1671665987971530397621250608750704078090294186961186396959185775229829) * 10 ^ 70 +
        5608057855214194870615711904822765805432303265230003941114274773651217) * 10 ^ 70 +
        5627514923039619874194580250731319141919480768296764963121699981421239) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (299 - x)) = _
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
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 9 +
      131 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (300 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_300 :
    recurrence4Scalar2Second.coeff 300 =
      -(((((3158299859552003938811 * 10 ^ 70 +
        7586260964748519255847289266166973099292041111124450966737841151493759) * 10 ^ 70 +
        9330200554196717103098697425505119506402087773782577279755232606268960) * 10 ^ 70 +
        5861941692076154878748646246603707215825967900553777524453043190132480) * 10 ^ 70 +
        4987652474655411290518906694204241749919262573872587454306892478519331) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (300 - x)) = _
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
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 9 +
      132 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (301 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_301 :
    recurrence4Scalar2Second.coeff 301 =
      (((((2960882257395221681985 * 10 ^ 70 +
        0524319379567714870584060159991844491966047011069230232462684892011430) * 10 ^ 70 +
        7407794395670075794717543265247118887708940122895233851009489584573956) * 10 ^ 70 +
        9992488387016701178297875745685083410427898604847828459482722459527538) * 10 ^ 70 +
        6034635671804714791620456771422036774397291497237632181154274827895528) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (301 - x)) = _
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
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 9 +
      133 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (302 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_302 :
    recurrence4Scalar2Second.coeff 302 =
      -(((((2397808796990922303844 * 10 ^ 70 +
        8281651245969530831064055662726398423057674600417135781754842531273461) * 10 ^ 70 +
        9337428178130051984951751090604842216171496193766087600355139206340888) * 10 ^ 70 +
        2027565555505767545686170400467036254131955652197444147336130712213383) * 10 ^ 70 +
        7754355093781726675493416086762889149319263235043008802332285658370474) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (302 - x)) = _
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
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 9 +
      134 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (303 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_303 :
    recurrence4Scalar2Second.coeff 303 =
      (((((1786271628011536291180 * 10 ^ 70 +
        0119488357279229407946689243199548546087917627083713498656275393228798) * 10 ^ 70 +
        9883879747078891056837364343897633810359135311990956800167744351167142) * 10 ^ 70 +
        6045524459427556467840849168669075526052176322313192210857211838910769) * 10 ^ 70 +
        0935363717937898367162762931135265559286504308462346651998028404322009) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (303 - x)) = _
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
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 9 +
      135 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (304 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_304 :
    recurrence4Scalar2Second.coeff 304 =
      -(((((1257259165250066182576 * 10 ^ 70 +
        9656053703516549679440997929544994083599588507746707250682245620129552) * 10 ^ 70 +
        0295148467418660824053045419503248080452797995120833611446856978084714) * 10 ^ 70 +
        6029067315491812662984590125981288619733428616718382248066031671151947) * 10 ^ 70 +
        5134890205912883605685763506672482608491460391969924937875186217219232) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (304 - x)) = _
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
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 9 +
      136 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (305 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_305 :
    recurrence4Scalar2Second.coeff 305 =
      (((((847663108890951293460 * 10 ^ 70 +
        3770025413860124122158012948372648389201145700867524168565371626004411) * 10 ^ 70 +
        7839387215933854751503063702323221097978590239284927233390204858327518) * 10 ^ 70 +
        2221791913533628998725092041248364702564723597652728650314927834225652) * 10 ^ 70 +
        1721173899724426661687705447548028334488448241920168267285465037935391) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (305 - x)) = _
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
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 9 +
      137 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (306 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_306 :
    recurrence4Scalar2Second.coeff 306 =
      -(((((551793119035177453264 * 10 ^ 70 +
        4173383481486614861991483724215771454795674350464521416961777366936787) * 10 ^ 70 +
        8579359619220489026588892798574822968832210347376804831184937070445051) * 10 ^ 70 +
        1959806174538785795948700058961149177236876186962141386587272431080811) * 10 ^ 70 +
        9650771824871037527046149544275241503508875817888005410318611070666583) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (306 - x)) = _
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
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 9 +
      138 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (307 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_307 :
    recurrence4Scalar2Second.coeff 307 =
      (((((348481989960627060580 * 10 ^ 70 +
        0141912477852201681639288981302680855596215673866220708516537248137327) * 10 ^ 70 +
        3767269304158641547332992511758079845798403616935263183626439831388615) * 10 ^ 70 +
        0542679570387446592792276743755898213903335826588537332398400101278865) * 10 ^ 70 +
        5409824973773401416022470101963833525716529357257478907019859174595268) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (307 - x)) = _
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
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 9 +
      139 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (308 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_308 :
    recurrence4Scalar2Second.coeff 308 =
      -(((((214162547608151658413 * 10 ^ 70 +
        9392542396251794930407355572191444050451479484721976870215388383925128) * 10 ^ 70 +
        2171967397675292758253044634364305924534366691407154904898021138022950) * 10 ^ 70 +
        7349059669978285810503240961502097995617688587128755755731331848899946) * 10 ^ 70 +
        1909832858187258213975743628019922280514785937356470317642245963895724) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (308 - x)) = _
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
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 9 +
      140 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (309 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_309 :
    recurrence4Scalar2Second.coeff 309 =
      (((((128309473538157266119 * 10 ^ 70 +
        7260145623629924742109387998911306009600055756155449738654117525934789) * 10 ^ 70 +
        2170505400208665389722513230239438802671205319913414917667351912596304) * 10 ^ 70 +
        4539478798907164520432859352664668473212552615221950217061024368333762) * 10 ^ 70 +
        5389429538167599767485828212989717844017613866883823686682820485501030) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (309 - x)) = _
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
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 9 +
      141 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (310 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_310 :
    recurrence4Scalar2Second.coeff 310 =
      -(((((75014438387879097386 * 10 ^ 70 +
        9164682818308361348053377672820993518973681861645199621858679482399135) * 10 ^ 70 +
        4162609991874797715895514310929339178342582803018540147088229503023559) * 10 ^ 70 +
        0326322102196750257458981051679247945372968730816314337634601764547892) * 10 ^ 70 +
        8700774519041768375790371873015704306669445340612497625721471832495273) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (310 - x)) = _
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
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 9 +
      142 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (311 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_311 :
    recurrence4Scalar2Second.coeff 311 =
      (((((42807039867042015457 * 10 ^ 70 +
        5958985712910751185473206818545301491802095535146786213390017249307339) * 10 ^ 70 +
        1800186020449780232449245360145292065857326221490086667386589116568171) * 10 ^ 70 +
        0184203061109199102143829329242462409231296305186688948327280821431555) * 10 ^ 70 +
        2144144879152224298815403528111783947468791302022624365736281443342532) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (311 - x)) = _
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
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 9 +
      143 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (312 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_312 :
    recurrence4Scalar2Second.coeff 312 =
      -(((((23834001532131062437 * 10 ^ 70 +
        2074665454212585316310513714433585165777909258696086971192280156893120) * 10 ^ 70 +
        2505945288138621596600707288663761744712182719658409565879567507670004) * 10 ^ 70 +
        9407950354496866348716068231679597030724000381115938141321036715401488) * 10 ^ 70 +
        0452054262851108554882223623505599758728286323879312513887858975641776) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (312 - x)) = _
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
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 9 +
      144 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (313 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_313 :
    recurrence4Scalar2Second.coeff 313 =
      (((((12933277041835473578 * 10 ^ 70 +
        9803339331946121134080698712056339353184794228461473301638932902115724) * 10 ^ 70 +
        2250011560581647670372037418050549386712570655518133457921019443153783) * 10 ^ 70 +
        5430136178962054946262505141154889718109463928818874825610781080966248) * 10 ^ 70 +
        1707457391693860525407063561388546663970945035450901156938914686869847) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (313 - x)) = _
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
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 9 +
      145 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (314 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_314 :
    recurrence4Scalar2Second.coeff 314 =
      -(((((6826314821385306612 * 10 ^ 70 +
        7427035887104210208445241041451172237583234012295204109886898010520081) * 10 ^ 70 +
        3844308245984214463007004793923088485815138092692081644402490698004151) * 10 ^ 70 +
        3998535965066601016936459897487358493698060735280427152353149532832153) * 10 ^ 70 +
        4457409480082344560138794583591086204640172390724764077053009927089550) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (314 - x)) = _
  rw [show 315 = 0 +
    315 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 9 +
      146 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (315 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_315 :
    recurrence4Scalar2Second.coeff 315 =
      (((((3493276745670053801 * 10 ^ 70 +
        2588066474405007895788859692005274833663426807345811159682913914410330) * 10 ^ 70 +
        3514301825933209584468824488276243370997947924741791683000906828122107) * 10 ^ 70 +
        6164912452075945037549679303851628434228331393337939406471043004498324) * 10 ^ 70 +
        5658198194787192201831591164954574543725522951793024051607891299142296) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (315 - x)) = _
  rw [show 316 = 0 +
    316 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 316 = 32 +
      284 by norm_num, Finset.sum_range_add]
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
    rw [show 156 = 9 +
      147 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (316 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_316 :
    recurrence4Scalar2Second.coeff 316 =
      -(((((1724340918298957564 * 10 ^ 70 +
        4730044325946415277987538685132849379316958683095069811176448175420532) * 10 ^ 70 +
        8060063669957511228182697954106958774753366886530688804035613402966590) * 10 ^ 70 +
        2305997317611982181984419966463124891007340739351135468024631640643914) * 10 ^ 70 +
        9202673324902594879358361576574308047323068869382888065611530839492966) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (316 - x)) = _
  rw [show 317 = 0 +
    317 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 317 = 32 +
      285 by norm_num, Finset.sum_range_add]
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
    rw [show 157 = 9 +
      148 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (317 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_317 :
    recurrence4Scalar2Second.coeff 317 =
      (((((814149802527489526 * 10 ^ 70 +
        3603850464146809878950728944429416189006118605285426800892826033006097) * 10 ^ 70 +
        4443606163216808295349636040634484834694711071032472938604278981700992) * 10 ^ 70 +
        4241509093639028931548857840097238666926158144240911301652911434742607) * 10 ^ 70 +
        2545917056691780004436237240663831948597182173018639620929889937298486) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (317 - x)) = _
  rw [show 318 = 0 +
    318 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 318 = 32 +
      286 by norm_num, Finset.sum_range_add]
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
    rw [show 158 = 9 +
      149 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (318 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_318 :
    recurrence4Scalar2Second.coeff 318 =
      -(((((362291971084279449 * 10 ^ 70 +
        7871149498654464042557062152691245167565282183709543307952470711815902) * 10 ^ 70 +
        2827156713435477448994156020685130265006327306567436293134673388736523) * 10 ^ 70 +
        0139385728188332713549252208274179756319976551909157321470585339845069) * 10 ^ 70 +
        7840540761249775805095212489860283434797580004318715176693572285366395) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (318 - x)) = _
  rw [show 319 = 0 +
    319 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 319 = 32 +
      287 by norm_num, Finset.sum_range_add]
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
    rw [show 159 = 9 +
      150 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (319 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_319 :
    recurrence4Scalar2Second.coeff 319 =
      (((((147570288028413073 * 10 ^ 70 +
        4540384513570271272844630324308556125138316188120926691753131151507569) * 10 ^ 70 +
        9117228661855584304080166409189393406240864837353161677588142076371498) * 10 ^ 70 +
        4080861423700843678078367958755628279037987432253312218889304954947261) * 10 ^ 70 +
        8529758129010362329572241584709355059094535241616115844535733590399491) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (319 - x)) = _
  rw [show 320 = 0 +
    320 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 320 = 32 +
      288 by norm_num, Finset.sum_range_add]
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
    rw [show 160 = 9 +
      151 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (320 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_320 :
    recurrence4Scalar2Second.coeff 320 =
      -(((((51243623628564972 * 10 ^ 70 +
        4512502912561195592781082425618513359272890175836037565294700986227777) * 10 ^ 70 +
        6349298681302962175916360742944697143110737789601801547119945345643650) * 10 ^ 70 +
        8628178432154423144261061733653527726629226393359102187893167490678563) * 10 ^ 70 +
        3720870182125746559579923414549673105423972250034232434278476136650583) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (320 - x)) = _
  rw [show 321 = 0 +
    321 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 321 = 32 +
      289 by norm_num, Finset.sum_range_add]
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
    rw [show 161 = 9 +
      152 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (321 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_321 :
    recurrence4Scalar2Second.coeff 321 =
      (((((11532892807728431 * 10 ^ 70 +
        8813364049199400057443850733993167632666104786877184642047011820441400) * 10 ^ 70 +
        7369954582212796246081576195762075896326062330905638214453311090192380) * 10 ^ 70 +
        9761705102903782195413605672243578217730943092823810472271989196437232) * 10 ^ 70 +
        7323444357058759075245883889904437792748678544268148181372563677503605) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (321 - x)) = _
  rw [show 322 = 0 +
    322 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 322 = 32 +
      290 by norm_num, Finset.sum_range_add]
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
    rw [show 162 = 9 +
      153 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (322 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_322 :
    recurrence4Scalar2Second.coeff 322 =
      (((((2581552687645464 * 10 ^ 70 +
        9785688496611404529761258127235640024283954954883183809121161906828910) * 10 ^ 70 +
        3964269792106920550566164330688261038448955597769110676150936634108277) * 10 ^ 70 +
        8156718470841115476012652813320557923258236036999850605651028445141562) * 10 ^ 70 +
        7282837104345115842980637708380090363560990085539403731727797914567650) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (322 - x)) = _
  rw [show 323 = 0 +
    323 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 323 = 32 +
      291 by norm_num, Finset.sum_range_add]
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
    rw [show 163 = 9 +
      154 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (323 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_323 :
    recurrence4Scalar2Second.coeff 323 =
      -(((((6024882519969523 * 10 ^ 70 +
        7723463221922231519751687854439279346804226719702118765415752858577141) * 10 ^ 70 +
        5836042792823061045484752598697435616155600395950775496212802221603836) * 10 ^ 70 +
        9685234051739979468079978006696358469361502343846329666856482334141274) * 10 ^ 70 +
        0229964171541168125506101048942142615304107812176051600200103019681743) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (323 - x)) = _
  rw [show 324 = 0 +
    324 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 324 = 32 +
      292 by norm_num, Finset.sum_range_add]
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
    rw [show 164 = 9 +
      155 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
