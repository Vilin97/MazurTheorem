/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59

attribute [local simp]
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
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
  recurrence4QuotientConstant_coeff_123

attribute [local simp]
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
  recurrence4QuotientConstant_coeff_187

attribute [local simp]
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
  recurrence4QuotientConstant_coeff_251

attribute [local simp]
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
  recurrence4QuotientConstant_coeff_315

attribute [local simp]
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

private theorem recurrence4Scalar1Second_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (329 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (329 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_329 :
    recurrence4Scalar1Second.coeff 329 =
      (((((1564948852488946 * 10 ^ 70 +
        5002284416799171889326670652693554830635590668414042253546631750757042) * 10 ^ 70 +
        4929955032225618770305671271169460752491280172048703408377601261092780) * 10 ^ 70 +
        7967214195604257592775016640143154641871942029017213637278812431154430) * 10 ^ 70 +
        0679219101078906535356640684667498332104539683559143429977680659293015) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (329 - x)) = _
  rw [show 330 = 1 +
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
    rw [show 169 = 12 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (330 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (330 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_330 :
    recurrence4Scalar1Second.coeff 330 =
      -(((((284068805941796 * 10 ^ 70 +
        5264892449291446989172676329973938740822210208469070259180880968683296) * 10 ^ 70 +
        3223790562027551388433424041604945852112490821978342789480749048434540) * 10 ^ 70 +
        3388246223839525152374786901326012053669748622252412334623636603962307) * 10 ^ 70 +
        5547168344594555341385629612501415512629613656392991181432224337752416) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (330 - x)) = _
  rw [show 331 = 1 +
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
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (331 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (331 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_331 :
    recurrence4Scalar1Second.coeff 331 =
      -(((((91388241949117 * 10 ^ 70 +
        1554450940794323706727639428659157305204806950936929272851125812504173) * 10 ^ 70 +
        4862896977283963510185170256357825374787037123769366912281883161330487) * 10 ^ 70 +
        0625965027391067559461608574579976542273283980080852980293000773705036) * 10 ^ 70 +
        2689547730648856894973362819140434907188494675781797064851380446493607) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (331 - x)) = _
  rw [show 332 = 1 +
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
    rw [show 171 = 12 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (332 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (332 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_332 :
    recurrence4Scalar1Second.coeff 332 =
      (((((149732367351428 * 10 ^ 70 +
        2168421658703280369210554731067995932435179601461437300551057861307918) * 10 ^ 70 +
        7171034710791322574325701494661381026879674144923662281554834711545112) * 10 ^ 70 +
        5293047365929670664909288310505508953206803478970954163282418953483757) * 10 ^ 70 +
        0074681153205448371053757214856029640160486870422953287504632068338550) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (332 - x)) = _
  rw [show 333 = 1 +
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
    rw [show 172 = 12 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (333 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (333 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_333 :
    recurrence4Scalar1Second.coeff 333 =
      -(((((118635511584991 * 10 ^ 70 +
        7143010144914365499900245153323778978547803346418695089108603930149673) * 10 ^ 70 +
        8229767145572184102777866356995989829964337753977779862669393346141814) * 10 ^ 70 +
        5381115853106473066586746850564346791916982945814163108495567947997927) * 10 ^ 70 +
        0907146541216938367505894333704296531735880659252922803501546187619863) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (333 - x)) = _
  rw [show 334 = 1 +
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
    rw [show 173 = 12 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (334 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (334 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_334 :
    recurrence4Scalar1Second.coeff 334 =
      (((((76418359381077 * 10 ^ 70 +
        2282771969627363840133985009884878474476887224410394020506571416362641) * 10 ^ 70 +
        0291873935874210028149615602663831832053166375299113070414059056317527) * 10 ^ 70 +
        3839887939828364442590321836617876728145130041214347182647442980143497) * 10 ^ 70 +
        2063319446440599405444952832625827556950817484609868181834362190553812) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (334 - x)) = _
  rw [show 335 = 1 +
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
    rw [show 174 = 12 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (335 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (335 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_335 :
    recurrence4Scalar1Second.coeff 335 =
      -(((((44202133655079 * 10 ^ 70 +
        9648680232423649243850517703340018513786235627750020102733009427038929) * 10 ^ 70 +
        4864225327235392352503077942507974150369202429503396786371127343499641) * 10 ^ 70 +
        4861540444216792939981748375819848153233087719624160331888199881292293) * 10 ^ 70 +
        3703661387291229858366103315478622793100937148257487174835786107283366) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (335 - x)) = _
  rw [show 336 = 1 +
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
    rw [show 175 = 12 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (336 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (336 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_336 :
    recurrence4Scalar1Second.coeff 336 =
      (((((23818808112348 * 10 ^ 70 +
        8585577665061556522541652633966761623619903240265354471986863390345173) * 10 ^ 70 +
        9796649201550444054213708151277141499948603143898098966373171995650769) * 10 ^ 70 +
        2876305057943377828449649656261432823317103806788440380621036942430399) * 10 ^ 70 +
        7886213732983233764028363066911601813724757381000347602849611228917118) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (336 - x)) = _
  rw [show 337 = 1 +
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
    rw [show 176 = 12 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (337 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (337 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_337 :
    recurrence4Scalar1Second.coeff 337 =
      -(((((12166923266844 * 10 ^ 70 +
        2544804605165292462975354668601558273808465672646603850418795398289463) * 10 ^ 70 +
        6211541271948088220166951700592921280690365337060279805325916795322763) * 10 ^ 70 +
        7869237625160612983162549206807266275561576903860356852460408150517709) * 10 ^ 70 +
        0229297291386389358826426263449146274203575267761502628072482902414907) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (337 - x)) = _
  rw [show 338 = 1 +
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
    rw [show 177 = 12 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (338 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (338 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_338 :
    recurrence4Scalar1Second.coeff 338 =
      (((((5946477239518 * 10 ^ 70 +
        2911699997068631514394767841056197395254464270615242368527331242916170) * 10 ^ 70 +
        3397965647259513161861102410067512335609055125511501889875697875740309) * 10 ^ 70 +
        2152753065736358235821389355148862261611547353253110863770450728846069) * 10 ^ 70 +
        4877641758063788288918101971963400355780826691940464522125919603278011) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (338 - x)) = _
  rw [show 339 = 1 +
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
    rw [show 178 = 12 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (339 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (339 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_339 :
    recurrence4Scalar1Second.coeff 339 =
      -(((((2795219396364 * 10 ^ 70 +
        0881278632624474403704246151554384227696406869253103324131707460018754) * 10 ^ 70 +
        3395845613556906334465691439834480501401634635183649907979738791360381) * 10 ^ 70 +
        7451836783419799060243521888963129829416665844791895614122676046234070) * 10 ^ 70 +
        4654440512102835813675645662599037613787707700639157295618644536437433) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (339 - x)) = _
  rw [show 340 = 1 +
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
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (340 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (340 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_340 :
    recurrence4Scalar1Second.coeff 340 =
      (((((1267264266607 * 10 ^ 70 +
        9478991304638747974534497562825725419986135833466057495808976217872886) * 10 ^ 70 +
        4417275313480466014976938987827229052766457626790574302098903693422247) * 10 ^ 70 +
        3151976808293958210998338367818987922950178863900341089302182089874890) * 10 ^ 70 +
        6278199877545200053074968714517544983043636407975560528714125434514912) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (340 - x)) = _
  rw [show 341 = 1 +
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
    rw [show 180 = 12 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (341 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (341 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_341 :
    recurrence4Scalar1Second.coeff 341 =
      -(((((554783167830 * 10 ^ 70 +
        2090554907070674988204784863980498029547475228944248309966005458860261) * 10 ^ 70 +
        4931312398374771892486233194852841186697421079293046500153594031931141) * 10 ^ 70 +
        3026662175464122749331668900186410067524711465303214065560670576307711) * 10 ^ 70 +
        8888546009952782254964282115016506251593386268525778242709402934934771) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (341 - x)) = _
  rw [show 342 = 1 +
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
    rw [show 181 = 12 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (342 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (342 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_342 :
    recurrence4Scalar1Second.coeff 342 =
      (((((234489189767 * 10 ^ 70 +
        3568477183806866642659625589729870284423400283812997118692709139394204) * 10 ^ 70 +
        7509244081877590975208574286943831908127465695727082597888223089525443) * 10 ^ 70 +
        7820236651279140133754060929620216209683567436321000990855759218949628) * 10 ^ 70 +
        0788097248935923727642847800525241374070581440685693405659664796665852) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (342 - x)) = _
  rw [show 343 = 1 +
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
    rw [show 182 = 12 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (343 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (343 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_343 :
    recurrence4Scalar1Second.coeff 343 =
      -(((((95553772268 * 10 ^ 70 +
        5263849980298275536506988762816260760061322775648605076555191008836153) * 10 ^ 70 +
        6491109183393198895236431843168725765315324027126896764548552934217175) * 10 ^ 70 +
        5790363556435226806310010194525090607672764285093205476605499719573578) * 10 ^ 70 +
        7138110435121276370515908974583335572895054722283003812673364295409233) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (343 - x)) = _
  rw [show 344 = 1 +
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
    rw [show 183 = 12 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (344 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (344 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_344 :
    recurrence4Scalar1Second.coeff 344 =
      (((((37430392709 * 10 ^ 70 +
        2274880251187195290919574908926633354274191816284732199442480411442158) * 10 ^ 70 +
        8457003292626280360465826401353039557194952033916779279025539408666855) * 10 ^ 70 +
        1485888478893403426992500185423533642069640898420728986536026554620795) * 10 ^ 70 +
        9040936578825493032621110998486428814207856084117613024709426305286508) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (344 - x)) = _
  rw [show 345 = 1 +
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
    rw [show 184 = 12 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (345 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (345 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_345 :
    recurrence4Scalar1Second.coeff 345 =
      -(((((14023791235 * 10 ^ 70 +
        4565468965022275676633410937556441709073706765841502340401041602135504) * 10 ^ 70 +
        6967283154012481475374882933763281374698887446528239307939810822956949) * 10 ^ 70 +
        5431950015836006566380832050840751785309028549728684140135858546962000) * 10 ^ 70 +
        2188190665064307752623451033500774344500716408589544134360602146028137) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (345 - x)) = _
  rw [show 346 = 1 +
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
    rw [show 185 = 12 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (346 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (346 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_346 :
    recurrence4Scalar1Second.coeff 346 =
      (((((4983303542 * 10 ^ 70 +
        3697350076132061901097435397729013616198744071316082560387651466473525) * 10 ^ 70 +
        3748924767067185967391631390848913191001568708525978780331128441448708) * 10 ^ 70 +
        7026785074227459100430813666395266119753991744045127000255373397053261) * 10 ^ 70 +
        4687883873665776966778576962547977749705452439795674118993807072404070) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (346 - x)) = _
  rw [show 347 = 1 +
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
    rw [show 186 = 12 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (347 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (347 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_347 :
    recurrence4Scalar1Second.coeff 347 =
      -(((((1655091068 * 10 ^ 70 +
        9856990734010452171795339540954628931716011290713724887256837873706627) * 10 ^ 70 +
        9314851066276395230476531499407034844062536005909063821792789207992264) * 10 ^ 70 +
        4034396907566737093988036521536066968736789504669329350105272096669518) * 10 ^ 70 +
        4320381102672448524350899259853941027429730650624244001990961353814207) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (347 - x)) = _
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
    rw [show 187 = 12 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (348 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (348 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_348 :
    recurrence4Scalar1Second.coeff 348 =
      (((((499513176 * 10 ^ 70 +
        2012053249728911176476588436935987093894155844192126555029306183058560) * 10 ^ 70 +
        2988263044682779874727081396864011027799626193339033836316005313283786) * 10 ^ 70 +
        6461974610004071636454062798325892156976104172396401590795464236329433) * 10 ^ 70 +
        6585876352924479854519049620866142494132218621599762683015261247728491) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (348 - x)) = _
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
    rw [show 187 = 11 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (349 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (349 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_349 :
    recurrence4Scalar1Second.coeff 349 =
      -(((((128299472 * 10 ^ 70 +
        2700587375529324322248026993449919968273772122054976075226680388148525) * 10 ^ 70 +
        4434958396946960596083321020849497489336902645542172334385709001779783) * 10 ^ 70 +
        2685129443437834213955371390285585132841195502539858444576451374772846) * 10 ^ 70 +
        9505230102923452327804292633384776885318157391036302383898591448315762) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (349 - x)) = _
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
    rw [show 187 = 10 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (350 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (350 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_350 :
    recurrence4Scalar1Second.coeff 350 =
      (((((22265248 * 10 ^ 70 +
        6509560275657764650187438565274459792087406552224759338383614072181406) * 10 ^ 70 +
        7215669302051831154297684216788534629621529056655130048944413922370453) * 10 ^ 70 +
        9793215818983655665853392143430441123383993117919444446819571218900668) * 10 ^ 70 +
        6443278337489699153451276808050919293916624922909197654443089435703880) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (350 - x)) = _
  rw [show 351 = 4 +
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
  rw [recurrence4Scalar1Second_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (351 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (351 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_351 :
    recurrence4Scalar1Second.coeff 351 =
      (((((1947680 * 10 ^ 70 +
        6844471034796808775993083411324599079771458363160516584711378400477860) * 10 ^ 70 +
        3091667224223912786028375860204082853636799872715135532300774586046771) * 10 ^ 70 +
        6965744813661161035345261308569812967244502988154377844076071871154724) * 10 ^ 70 +
        7841256995403067391721051773782433512269257421765657814435926795610872) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (351 - x)) = _
  rw [show 352 = 5 +
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
  rw [recurrence4Scalar1Second_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (352 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (352 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_352 :
    recurrence4Scalar1Second.coeff 352 =
      -(((((4429647 * 10 ^ 70 +
        5995810997740324804685867986760306712771405357998200845658600227420134) * 10 ^ 70 +
        8073051016227687061970725515388163868705679558389023524598079191691469) * 10 ^ 70 +
        5762076652170489464387577896272632839998125579339361751899731947026859) * 10 ^ 70 +
        8849088582958839191595866897069143503908701196702320660747278929533858) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (352 - x)) = _
  rw [show 353 = 6 +
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
  rw [recurrence4Scalar1Second_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (353 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (353 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_353 :
    recurrence4Scalar1Second.coeff 353 =
      (((((2814664 * 10 ^ 70 +
        9351169493818072339389760232301118164783988498590482328205101103283407) * 10 ^ 70 +
        9581862274113247872404466259320900457608420283964129104505872756340062) * 10 ^ 70 +
        5026600931171189700045787673289931800218481697745925312455009898286750) * 10 ^ 70 +
        1660521555572832830625397159946509606436591852790496782877817317306318) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (353 - x)) = _
  rw [show 354 = 7 +
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
  rw [recurrence4Scalar1Second_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Second_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (354 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (354 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_354 :
    recurrence4Scalar1Second.coeff 354 =
      -(((((1330199 * 10 ^ 70 +
        0125073169391910126565367055095551849819376614754319164410442957320281) * 10 ^ 70 +
        1120015074651738933624778340546228750209323323813544636480936721218505) * 10 ^ 70 +
        3802312274103764514391487654145015863040634449691806492350583662911362) * 10 ^ 70 +
        9607361002619707384313721313644889522752968568778721957073912090283265) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (354 - x)) = _
  rw [show 355 = 8 +
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
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
