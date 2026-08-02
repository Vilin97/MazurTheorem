/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_0
  recurrence5ExceptionalProduct_coeff_1
  recurrence5ExceptionalProduct_coeff_2
  recurrence5ExceptionalProduct_coeff_3
  recurrence5ExceptionalProduct_coeff_4
  recurrence5ExceptionalProduct_coeff_5
  recurrence5ExceptionalProduct_coeff_6
  recurrence5ExceptionalProduct_coeff_7
  recurrence5ExceptionalProduct_coeff_8
  recurrence5ExceptionalProduct_coeff_9
  recurrence5ExceptionalProduct_coeff_10
  recurrence5ExceptionalProduct_coeff_11
  recurrence5ExceptionalProduct_coeff_12
  recurrence5ExceptionalProduct_coeff_13
  recurrence5ExceptionalProduct_coeff_14
  recurrence5ExceptionalProduct_coeff_15
  recurrence5ExceptionalProduct_coeff_16
  recurrence5ExceptionalProduct_coeff_17
  recurrence5ExceptionalProduct_coeff_18
  recurrence5ExceptionalProduct_coeff_19
  recurrence5ExceptionalProduct_coeff_20
  recurrence5ExceptionalProduct_coeff_21
  recurrence5ExceptionalProduct_coeff_22
  recurrence5ExceptionalProduct_coeff_23
  recurrence5ExceptionalProduct_coeff_24
  recurrence5ExceptionalProduct_coeff_25
  recurrence5ExceptionalProduct_coeff_26
  recurrence5ExceptionalProduct_coeff_27
  recurrence5ExceptionalProduct_coeff_28
  recurrence5ExceptionalProduct_coeff_29
  recurrence5ExceptionalProduct_coeff_30
  recurrence5ExceptionalProduct_coeff_31
  recurrence5ExceptionalProduct_coeff_32
  recurrence5ExceptionalProduct_coeff_33
  recurrence5ExceptionalProduct_coeff_34
  recurrence5ExceptionalProduct_coeff_35
  recurrence5ExceptionalProduct_coeff_36
  recurrence5ExceptionalProduct_coeff_37
  recurrence5ExceptionalProduct_coeff_38
  recurrence5ExceptionalProduct_coeff_39
  recurrence5ExceptionalProduct_coeff_40
  recurrence5ExceptionalProduct_coeff_41
  recurrence5ExceptionalProduct_coeff_42
  recurrence5ExceptionalProduct_coeff_43
  recurrence5ExceptionalProduct_coeff_44
  recurrence5ExceptionalProduct_coeff_45
  recurrence5ExceptionalProduct_coeff_46
  recurrence5ExceptionalProduct_coeff_47
  recurrence5ExceptionalProduct_coeff_48
  recurrence5ExceptionalProduct_coeff_49
  recurrence5ExceptionalProduct_coeff_50
  recurrence5ExceptionalProduct_coeff_51
  recurrence5ExceptionalProduct_coeff_52
  recurrence5ExceptionalProduct_coeff_53
  recurrence5ExceptionalProduct_coeff_54
  recurrence5ExceptionalProduct_coeff_55
  recurrence5ExceptionalProduct_coeff_56
  recurrence5ExceptionalProduct_coeff_57
  recurrence5ExceptionalProduct_coeff_58
  recurrence5ExceptionalProduct_coeff_59
  recurrence5ExceptionalProduct_coeff_60
  recurrence5ExceptionalProduct_coeff_61
  recurrence5ExceptionalProduct_coeff_62
  recurrence5ExceptionalProduct_coeff_63

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_64
  recurrence5ExceptionalProduct_coeff_65
  recurrence5ExceptionalProduct_coeff_66
  recurrence5ExceptionalProduct_coeff_67
  recurrence5ExceptionalProduct_coeff_68
  recurrence5ExceptionalProduct_coeff_69
  recurrence5ExceptionalProduct_coeff_70
  recurrence5ExceptionalProduct_coeff_71
  recurrence5ExceptionalProduct_coeff_72
  recurrence5ExceptionalProduct_coeff_73
  recurrence5ExceptionalProduct_coeff_74
  recurrence5ExceptionalProduct_coeff_75
  recurrence5ExceptionalProduct_coeff_76
  recurrence5ExceptionalProduct_coeff_77
  recurrence5ExceptionalProduct_coeff_78
  recurrence5ExceptionalProduct_coeff_79
  recurrence5ExceptionalProduct_coeff_80
  recurrence5ExceptionalProduct_coeff_81
  recurrence5ExceptionalProduct_coeff_82
  recurrence5ExceptionalProduct_coeff_83
  recurrence5ExceptionalProduct_coeff_84
  recurrence5ExceptionalProduct_coeff_85
  recurrence5ExceptionalProduct_coeff_86
  recurrence5ExceptionalProduct_coeff_87
  recurrence5ExceptionalProduct_coeff_88
  recurrence5ExceptionalProduct_coeff_89
  recurrence5ExceptionalProduct_coeff_90
  recurrence5ExceptionalProduct_coeff_91
  recurrence5ExceptionalProduct_coeff_92
  recurrence5ExceptionalProduct_coeff_93
  recurrence5ExceptionalProduct_coeff_94
  recurrence5ExceptionalProduct_coeff_95
  recurrence5ExceptionalProduct_coeff_96
  recurrence5ExceptionalProduct_coeff_97
  recurrence5ExceptionalProduct_coeff_98
  recurrence5ExceptionalProduct_coeff_99
  recurrence5ExceptionalProduct_coeff_100
  recurrence5ExceptionalProduct_coeff_101
  recurrence5ExceptionalProduct_coeff_102
  recurrence5ExceptionalProduct_coeff_103
  recurrence5ExceptionalProduct_coeff_104
  recurrence5ExceptionalProduct_coeff_105
  recurrence5ExceptionalProduct_coeff_106
  recurrence5ExceptionalProduct_coeff_107
  recurrence5ExceptionalProduct_coeff_108
  recurrence5ExceptionalProduct_coeff_109
  recurrence5ExceptionalProduct_coeff_110
  recurrence5ExceptionalProduct_coeff_111
  recurrence5ExceptionalProduct_coeff_112
  recurrence5ExceptionalProduct_coeff_113
  recurrence5ExceptionalProduct_coeff_114
  recurrence5ExceptionalProduct_coeff_115
  recurrence5ExceptionalProduct_coeff_116
  recurrence5ExceptionalProduct_coeff_117
  recurrence5ExceptionalProduct_coeff_118
  recurrence5ExceptionalProduct_coeff_119
  recurrence5ExceptionalProduct_coeff_120
  recurrence5ExceptionalProduct_coeff_121
  recurrence5ExceptionalProduct_coeff_122
  recurrence5ExceptionalProduct_coeff_123
  recurrence5ExceptionalProduct_coeff_124
  recurrence5ExceptionalProduct_coeff_125
  recurrence5ExceptionalProduct_coeff_126
  recurrence5ExceptionalProduct_coeff_127

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_128
  recurrence5ExceptionalProduct_coeff_129
  recurrence5ExceptionalProduct_coeff_130
  recurrence5ExceptionalProduct_coeff_131
  recurrence5ExceptionalProduct_coeff_132
  recurrence5ExceptionalProduct_coeff_133
  recurrence5ExceptionalProduct_coeff_134
  recurrence5ExceptionalProduct_coeff_135
  recurrence5ExceptionalProduct_coeff_136
  recurrence5ExceptionalProduct_coeff_137
  recurrence5ExceptionalProduct_coeff_138
  recurrence5ExceptionalProduct_coeff_139
  recurrence5ExceptionalProduct_coeff_140
  recurrence5ExceptionalProduct_coeff_141
  recurrence5ExceptionalProduct_coeff_142
  recurrence5ExceptionalProduct_coeff_143
  recurrence5ExceptionalProduct_coeff_144
  recurrence5ExceptionalProduct_coeff_145
  recurrence5ExceptionalProduct_coeff_146
  recurrence5ExceptionalProduct_coeff_147
  recurrence5ExceptionalProduct_coeff_148
  recurrence5ExceptionalProduct_coeff_149
  recurrence5ExceptionalProduct_coeff_150
  recurrence5ExceptionalProduct_coeff_151
  recurrence5ExceptionalProduct_coeff_152
  recurrence5ExceptionalProduct_coeff_153
  recurrence5ExceptionalProduct_coeff_154
  recurrence5ExceptionalProduct_coeff_155
  recurrence5ExceptionalProduct_coeff_156
  recurrence5ExceptionalProduct_coeff_157
  recurrence5ExceptionalProduct_coeff_158
  recurrence5ExceptionalProduct_coeff_159
  recurrence5ExceptionalProduct_coeff_160
  recurrence5ExceptionalProduct_coeff_161
  recurrence5ExceptionalProduct_coeff_162
  recurrence5ExceptionalProduct_coeff_163
  recurrence5ExceptionalProduct_coeff_164
  recurrence5ExceptionalProduct_coeff_165
  recurrence5ExceptionalProduct_coeff_166
  recurrence5ExceptionalProduct_coeff_167
  recurrence5ExceptionalProduct_coeff_168
  recurrence5ExceptionalProduct_coeff_169
  recurrence5ExceptionalProduct_coeff_170
  recurrence5ExceptionalProduct_coeff_171
  recurrence5ExceptionalProduct_coeff_172
  recurrence5ExceptionalProduct_coeff_173
  recurrence5ExceptionalProduct_coeff_174
  recurrence5ExceptionalProduct_coeff_175
  recurrence5ExceptionalProduct_coeff_176
  recurrence5ExceptionalProduct_coeff_177
  recurrence5ExceptionalProduct_coeff_178
  recurrence5ExceptionalProduct_coeff_179
  recurrence5ExceptionalProduct_coeff_180
  recurrence5ExceptionalProduct_coeff_181
  recurrence5ExceptionalProduct_coeff_182
  recurrence5ExceptionalProduct_coeff_183
  recurrence5ExceptionalProduct_coeff_184
  recurrence5ExceptionalProduct_coeff_185
  recurrence5ExceptionalProduct_coeff_186
  recurrence5ExceptionalProduct_coeff_187
  recurrence5ExceptionalProduct_coeff_188
  recurrence5ExceptionalProduct_coeff_189
  recurrence5ExceptionalProduct_coeff_190
  recurrence5ExceptionalProduct_coeff_191

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_192
  recurrence5ExceptionalProduct_coeff_193
  recurrence5ExceptionalProduct_coeff_194
  recurrence5ExceptionalProduct_coeff_195
  recurrence5ExceptionalProduct_coeff_196
  recurrence5ExceptionalProduct_coeff_197
  recurrence5ExceptionalProduct_coeff_198
  recurrence5ExceptionalProduct_coeff_199
  recurrence5ExceptionalProduct_coeff_200
  recurrence5ExceptionalProduct_coeff_201
  recurrence5ExceptionalProduct_coeff_202
  recurrence5ExceptionalProduct_coeff_203
  recurrence5ExceptionalProduct_coeff_204
  recurrence5ExceptionalProduct_coeff_205
  recurrence5ExceptionalProduct_coeff_206
  recurrence5ExceptionalProduct_coeff_207
  recurrence5ExceptionalProduct_coeff_208
  recurrence5ExceptionalProduct_coeff_209
  recurrence5ExceptionalProduct_coeff_210
  recurrence5ExceptionalProduct_coeff_211
  recurrence5ExceptionalProduct_coeff_212
  recurrence5ExceptionalProduct_coeff_213
  recurrence5ExceptionalProduct_coeff_214
  recurrence5ExceptionalProduct_coeff_215
  recurrence5ExceptionalProduct_coeff_216
  recurrence5ExceptionalProduct_coeff_217
  recurrence5ExceptionalProduct_coeff_218
  recurrence5ExceptionalProduct_coeff_219
  recurrence5ExceptionalProduct_coeff_220
  recurrence5ExceptionalProduct_coeff_221
  recurrence5ExceptionalProduct_coeff_222
  recurrence5ExceptionalProduct_coeff_223
  recurrence5ExceptionalProduct_coeff_224
  recurrence5ExceptionalProduct_coeff_225
  recurrence5ExceptionalProduct_coeff_226
  recurrence5ExceptionalProduct_coeff_227
  recurrence5ExceptionalProduct_coeff_228
  recurrence5ExceptionalProduct_coeff_229
  recurrence5ExceptionalProduct_coeff_230
  recurrence5ExceptionalProduct_coeff_231
  recurrence5ExceptionalProduct_coeff_232
  recurrence5ExceptionalProduct_coeff_233
  recurrence5ExceptionalProduct_coeff_234
  recurrence5ExceptionalProduct_coeff_235
  recurrence5ExceptionalProduct_coeff_236
  recurrence5ExceptionalProduct_coeff_237
  recurrence5ExceptionalProduct_coeff_238
  recurrence5ExceptionalProduct_coeff_239
  recurrence5ExceptionalProduct_coeff_240
  recurrence5ExceptionalProduct_coeff_241
  recurrence5ExceptionalProduct_coeff_242
  recurrence5ExceptionalProduct_coeff_243
  recurrence5ExceptionalProduct_coeff_244
  recurrence5ExceptionalProduct_coeff_245
  recurrence5ExceptionalProduct_coeff_246
  recurrence5ExceptionalProduct_coeff_247
  recurrence5ExceptionalProduct_coeff_248
  recurrence5ExceptionalProduct_coeff_249
  recurrence5ExceptionalProduct_coeff_250
  recurrence5ExceptionalProduct_coeff_251
  recurrence5ExceptionalProduct_coeff_252
  recurrence5ExceptionalProduct_coeff_253
  recurrence5ExceptionalProduct_coeff_254
  recurrence5ExceptionalProduct_coeff_255

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_256
  recurrence5ExceptionalProduct_coeff_257
  recurrence5ExceptionalProduct_coeff_258
  recurrence5ExceptionalProduct_coeff_259
  recurrence5ExceptionalProduct_coeff_260
  recurrence5ExceptionalProduct_coeff_261
  recurrence5ExceptionalProduct_coeff_262
  recurrence5ExceptionalProduct_coeff_263
  recurrence5ExceptionalProduct_coeff_264
  recurrence5ExceptionalProduct_coeff_265
  recurrence5ExceptionalProduct_coeff_266
  recurrence5ExceptionalProduct_coeff_267
  recurrence5ExceptionalProduct_coeff_268
  recurrence5ExceptionalProduct_coeff_269
  recurrence5ExceptionalProduct_coeff_270
  recurrence5ExceptionalProduct_coeff_271
  recurrence5ExceptionalProduct_coeff_272
  recurrence5ExceptionalProduct_coeff_273
  recurrence5ExceptionalProduct_coeff_274
  recurrence5ExceptionalProduct_coeff_275
  recurrence5ExceptionalProduct_coeff_276
  recurrence5ExceptionalProduct_coeff_277
  recurrence5ExceptionalProduct_coeff_278
  recurrence5ExceptionalProduct_coeff_279
  recurrence5ExceptionalProduct_coeff_280
  recurrence5ExceptionalProduct_coeff_281
  recurrence5ExceptionalProduct_coeff_282
  recurrence5ExceptionalProduct_coeff_283
  recurrence5ExceptionalProduct_coeff_284
  recurrence5ExceptionalProduct_coeff_285
  recurrence5ExceptionalProduct_coeff_286
  recurrence5ExceptionalProduct_coeff_287
  recurrence5ExceptionalProduct_coeff_288
  recurrence5ExceptionalProduct_coeff_289
  recurrence5ExceptionalProduct_coeff_290
  recurrence5ExceptionalProduct_coeff_291
  recurrence5ExceptionalProduct_coeff_292
  recurrence5ExceptionalProduct_coeff_293
  recurrence5ExceptionalProduct_coeff_294
  recurrence5ExceptionalProduct_coeff_295
  recurrence5ExceptionalProduct_coeff_296
  recurrence5ExceptionalProduct_coeff_297
  recurrence5ExceptionalProduct_coeff_298
  recurrence5ExceptionalProduct_coeff_299
  recurrence5ExceptionalProduct_coeff_300
  recurrence5ExceptionalProduct_coeff_301
  recurrence5ExceptionalProduct_coeff_302
  recurrence5ExceptionalProduct_coeff_303
  recurrence5ExceptionalProduct_coeff_304
  recurrence5ExceptionalProduct_coeff_305
  recurrence5ExceptionalProduct_coeff_306
  recurrence5ExceptionalProduct_coeff_307
  recurrence5ExceptionalProduct_coeff_308
  recurrence5ExceptionalProduct_coeff_309
  recurrence5ExceptionalProduct_coeff_310
  recurrence5ExceptionalProduct_coeff_311
  recurrence5ExceptionalProduct_coeff_312
  recurrence5ExceptionalProduct_coeff_313
  recurrence5ExceptionalProduct_coeff_314
  recurrence5ExceptionalProduct_coeff_315
  recurrence5ExceptionalProduct_coeff_316
  recurrence5ExceptionalProduct_coeff_317
  recurrence5ExceptionalProduct_coeff_318
  recurrence5ExceptionalProduct_coeff_319

attribute [local simp]
  recurrence5ExceptionalProduct_coeff_320
  recurrence5ExceptionalProduct_coeff_321
  recurrence5ExceptionalProduct_coeff_322
  recurrence5ExceptionalProduct_coeff_323
  recurrence5ExceptionalProduct_coeff_324
  recurrence5ExceptionalProduct_coeff_325
  recurrence5ExceptionalProduct_coeff_326
  recurrence5ExceptionalProduct_coeff_327
  recurrence5ExceptionalProduct_coeff_328
  recurrence5ExceptionalProduct_coeff_329
  recurrence5ExceptionalProduct_coeff_330
  recurrence5ExceptionalProduct_coeff_331
  recurrence5ExceptionalProduct_coeff_332
  recurrence5ExceptionalProduct_coeff_333
  recurrence5ExceptionalProduct_coeff_334
  recurrence5ExceptionalProduct_coeff_335
  recurrence5ExceptionalProduct_coeff_336
  recurrence5ExceptionalProduct_coeff_337
  recurrence5ExceptionalProduct_coeff_338
  recurrence5ExceptionalProduct_coeff_339
  recurrence5ExceptionalProduct_coeff_340
  recurrence5ExceptionalProduct_coeff_341
  recurrence5ExceptionalProduct_coeff_342
  recurrence5ExceptionalProduct_coeff_343
  recurrence5ExceptionalProduct_coeff_344
  recurrence5ExceptionalProduct_coeff_345
  recurrence5ExceptionalProduct_coeff_346
  recurrence5ExceptionalProduct_coeff_347
  recurrence5ExceptionalProduct_coeff_348
  recurrence5ExceptionalProduct_coeff_349
  recurrence5ExceptionalProduct_coeff_350
  recurrence5ExceptionalProduct_coeff_351
  recurrence5ExceptionalProduct_coeff_352
  recurrence5ExceptionalProduct_coeff_353
  recurrence5ExceptionalProduct_coeff_354
  recurrence5ExceptionalProduct_coeff_355
  recurrence5ExceptionalProduct_coeff_356
  recurrence5ExceptionalProduct_coeff_357
  recurrence5ExceptionalProduct_coeff_358
  recurrence5ExceptionalProduct_coeff_359
  recurrence5ExceptionalProduct_coeff_360
  recurrence5ExceptionalProduct_coeff_361
  recurrence5ExceptionalProduct_coeff_362
  recurrence5ExceptionalProduct_coeff_363
  recurrence5ExceptionalProduct_coeff_364
  recurrence5ExceptionalProduct_coeff_365
  recurrence5ExceptionalProduct_coeff_366
  recurrence5ExceptionalProduct_coeff_367
  recurrence5ExceptionalProduct_coeff_368
  recurrence5ExceptionalProduct_coeff_369
  recurrence5ExceptionalProduct_coeff_370
  recurrence5ExceptionalProduct_coeff_371
  recurrence5ExceptionalProduct_coeff_372
  recurrence5ExceptionalProduct_coeff_373
  recurrence5ExceptionalProduct_coeff_374
  recurrence5ExceptionalProduct_coeff_375
  recurrence5ExceptionalProduct_coeff_376
  recurrence5ExceptionalProduct_coeff_377
  recurrence5ExceptionalProduct_coeff_378
  recurrence5C1_coeff_0
  recurrence5C1_coeff_1
  recurrence5C1_coeff_2
  recurrence5C1_coeff_3
  recurrence5C1_coeff_4

attribute [local simp]
  recurrence5C1_coeff_5
  recurrence5C1_coeff_6
  recurrence5C1_coeff_7
  recurrence5C1_coeff_8
  recurrence5C1_coeff_9
  recurrence5C1_coeff_10
  recurrence5C1_coeff_11
  recurrence5C1_coeff_12
  recurrence5C1_coeff_13
  recurrence5C1_coeff_14
  recurrence5C1_coeff_15
  recurrence5C1_coeff_16
  recurrence5C1_coeff_17
  recurrence5C1_coeff_18
  recurrence5C1_coeff_19
  recurrence5C1_coeff_20
  recurrence5C1_coeff_21
  recurrence5C1_coeff_22
  recurrence5C1_coeff_23
  recurrence5C1_coeff_24
  recurrence5C1_coeff_25
  recurrence5C1_coeff_26
  recurrence5C1_coeff_27
  recurrence5C1_coeff_28
  recurrence5C1_coeff_29
  recurrence5C1_coeff_30
  recurrence5C1_coeff_31
  recurrence5C1_coeff_32
  recurrence5C1_coeff_33
  recurrence5C1_coeff_34
  recurrence5C1_coeff_35
  recurrence5C1_coeff_36
  recurrence5C1_coeff_37
  recurrence5C1_coeff_38
  recurrence5C1_coeff_39
  recurrence5C1_coeff_40
  recurrence5C1_coeff_41
  recurrence5C1_coeff_42
  recurrence5C1_coeff_43
  recurrence5C1_coeff_44
  recurrence5C1_coeff_45
  recurrence5C1_coeff_46
  recurrence5C1_coeff_47
  recurrence5C1_coeff_48
  recurrence5C1_coeff_49
  recurrence5C1_coeff_50
  recurrence5C1_coeff_51
  recurrence5C1_coeff_52
  recurrence5C1_coeff_53
  recurrence5C1_coeff_54
  recurrence5C1_coeff_55
  recurrence5C1_coeff_56
  recurrence5C1_coeff_57
  recurrence5C1_coeff_58
  recurrence5C1_coeff_59
  recurrence5C1_coeff_60
  recurrence5C1_coeff_61
  recurrence5C1_coeff_62
  recurrence5C1_coeff_63
  recurrence5C1_coeff_64
  recurrence5C1_coeff_65
  recurrence5C1_coeff_66
  recurrence5C1_coeff_67
  recurrence5C1_coeff_68

attribute [local simp]
  recurrence5C1_coeff_69
  recurrence5C1_coeff_70
  recurrence5C1_coeff_71
  recurrence5C1_coeff_72
  recurrence5C1_coeff_73
  recurrence5C1_coeff_74
  recurrence5C1_coeff_75
  recurrence5C1_coeff_76
  recurrence5C1_coeff_77
  recurrence5C1_coeff_78
  recurrence5C1_coeff_79
  recurrence5C1_coeff_80
  recurrence5C1_coeff_81
  recurrence5C1_coeff_82
  recurrence5C1_coeff_83
  recurrence5C1_coeff_84

private theorem recurrence5Scalar1Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_219 :
    recurrence5Scalar1Exceptional.coeff 219 =
      ((((((8171358 * 10 ^ 70 +
        1874890636618139433033419742676499622343188088271010510610962951907005) * 10 ^ 70 +
        4642835747121620948735380809084120032456009515097744651682697489478989) * 10 ^ 70 +
        1849241524668612888897165027974581581906599839363015403181354945754327) * 10 ^ 70 +
        7887906501244382964642301512860216047865289124765188514327200378084107) * 10 ^ 70 +
        1585816567868335246453684959937061639078820266545949806195898554277996) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 135 +
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
  rw [recurrence5Scalar1Exceptional_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_220 :
    recurrence5Scalar1Exceptional.coeff 220 =
      -((((((7648317 * 10 ^ 70 +
        7294655383788346898571084292230909886742196154596075150316046988218957) * 10 ^ 70 +
        9502204766578836017192895611619013262558934438912188438212085242472348) * 10 ^ 70 +
        4173381864491758666771860784601369819324441809744520898123566778958182) * 10 ^ 70 +
        2351296903364237072715386191870132642490124098412671288640610018536331) * 10 ^ 70 +
        1587749802098011579276281965526379943244467332225956058312547246923396) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 136 +
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
  rw [recurrence5Scalar1Exceptional_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_221 :
    recurrence5Scalar1Exceptional.coeff 221 =
      ((((((6837798 * 10 ^ 70 +
        1136493508124252030650586601279655060534750178518369221280309706964486) * 10 ^ 70 +
        8402684816251714083734231192941052775120138969615812192980173893286659) * 10 ^ 70 +
        9202206490403698135184747804563667964536628210651941571499966194093995) * 10 ^ 70 +
        9576390857833184169406053352917220121796791148034877464100102228286714) * 10 ^ 70 +
        8278408533271926478228949260939581777718027515161644974650005896545909) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 137 +
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
  rw [recurrence5Scalar1Exceptional_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_222 :
    recurrence5Scalar1Exceptional.coeff 222 =
      -((((((5771788 * 10 ^ 70 +
        6948792544150879092472046792265573520264631955072964126659395792458471) * 10 ^ 70 +
        2714670366123722126874994352899144957496538978204684197482523298622969) * 10 ^ 70 +
        4208029554957495932840177894348558644421189282057404033858934753588981) * 10 ^ 70 +
        2640298843992123103375116678067333707447143808024641389489056345098054) * 10 ^ 70 +
        7317947943034005692424581773007619262005966779759953820517979787616370) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 138 +
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
  rw [recurrence5Scalar1Exceptional_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_223 :
    recurrence5Scalar1Exceptional.coeff 223 =
      ((((((4504156 * 10 ^ 70 +
        9936586255992427648636519255555821298097691369704956351114223719685318) * 10 ^ 70 +
        2871826751591512633570366919068935419662437496877082656699072744315932) * 10 ^ 70 +
        5232771908587496521034833570444191932041156309840403649284589158799401) * 10 ^ 70 +
        7070756484176264007867802077895390741290583765645286051948990477032586) * 10 ^ 70 +
        3296812641079220972199147810700500746191903545181161206983921330670763) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 139 +
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
  rw [recurrence5Scalar1Exceptional_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_224 :
    recurrence5Scalar1Exceptional.coeff 224 =
      -((((((3106683 * 10 ^ 70 +
        1733682986209831924639322121497120543116679079903979737686839151172869) * 10 ^ 70 +
        7164019702035185761071199290764642306886972827402337089650083336909847) * 10 ^ 70 +
        9720944222778869620925159467642555437739769980667080866476450176694847) * 10 ^ 70 +
        4403893177081515845946098901136719114651787931259179539661217279420788) * 10 ^ 70 +
        7611420205940489298024195577087481780461021462802020286355979408663701) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 140 +
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
  rw [recurrence5Scalar1Exceptional_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_225 :
    recurrence5Scalar1Exceptional.coeff 225 =
      ((((((1662810 * 10 ^ 70 +
        1662102171296915085715960261887069693859706818240026387281530850957340) * 10 ^ 70 +
        1021390490234784359491193487321762353157975839151530381639687779468029) * 10 ^ 70 +
        6652705714896032156454023546416530082390074351854389213514080026314100) * 10 ^ 70 +
        9828545280927677779035170203786683889423044564855032413851720949475525) * 10 ^ 70 +
        0725041275394507637238975692350873072275707052916022872320497586182046) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 141 +
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
  rw [recurrence5Scalar1Exceptional_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_226 :
    recurrence5Scalar1Exceptional.coeff 226 =
      -((((((259821 * 10 ^ 70 +
        7627976679104925846816662407384882961720355408052710789554314932112178) * 10 ^ 70 +
        4712064609185022669695326872497736971114681680118183303556385981688083) * 10 ^ 70 +
        8494744382564113471724603960058082074814148595796202802577882259927161) * 10 ^ 70 +
        2395970152653172158607139812209808196246567723358510342531671428396304) * 10 ^ 70 +
        5509405446695199843876284429826291504101966286897609424660500496410141) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 142 +
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
  rw [recurrence5Scalar1Exceptional_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_227 :
    recurrence5Scalar1Exceptional.coeff 227 =
      -((((((1019570 * 10 ^ 70 +
        9846607694493169395591271704734764114170910904657764688680436282335416) * 10 ^ 70 +
        4115691592205505478504211205305731589347666630530589221994148355604554) * 10 ^ 70 +
        8258483382069104391152931076576963768683371921287628468207552483513949) * 10 ^ 70 +
        5220197003542763852206984949415966707560149825544104988029345851594391) * 10 ^ 70 +
        0194930049826990923171763428662546114132556544019376117454218253168112) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 143 +
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
  rw [recurrence5Scalar1Exceptional_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_228 :
    recurrence5Scalar1Exceptional.coeff 228 =
      ((((((2105138 * 10 ^ 70 +
        7270145081873192260882387433651815109499186265852278568258808563234686) * 10 ^ 70 +
        8599121693896878555314186267808867497646319141759552829870868698469816) * 10 ^ 70 +
        6673371549381941057163691176022221217535749629310694714834115729579616) * 10 ^ 70 +
        0086529477569956916450278040471733368583235444165514852173939259221685) * 10 ^ 70 +
        1708923602435795527501954845521432167551671732118977678234295248328190) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 144 +
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
  rw [recurrence5Scalar1Exceptional_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_229 :
    recurrence5Scalar1Exceptional.coeff 229 =
      -((((((2945504 * 10 ^ 70 +
        2649756939591963478993810444630040524793465113282012150771651538658955) * 10 ^ 70 +
        3251954699955989103638867357127070749413942148913407999379802247639112) * 10 ^ 70 +
        7038732565302506816982690137499189834781048429566592441277840727375010) * 10 ^ 70 +
        8617529582078198341891093062648213275238732503758192973298137961898328) * 10 ^ 70 +
        3610606418344662882915608741381079517563981151052048633472751851107229) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 145 +
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
  rw [recurrence5Scalar1Exceptional_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_230 :
    recurrence5Scalar1Exceptional.coeff 230 =
      ((((((3512173 * 10 ^ 70 +
        1565005600137001953825089137345712690935120572542729004736561051662462) * 10 ^ 70 +
        0636658733728812856859134725822379717569300934701768140681569324368163) * 10 ^ 70 +
        3650366129569420700314840289464457001868290710381833090699762713326985) * 10 ^ 70 +
        9992913571526903994583634811310905424756765771361788083598755404736809) * 10 ^ 70 +
        4499987594925062098097583030278298773450730604167399521078443289720183) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 146 +
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
  rw [recurrence5Scalar1Exceptional_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_231 :
    recurrence5Scalar1Exceptional.coeff 231 =
      -((((((3800784 * 10 ^ 70 +
        0173518863261814616133107287356308673370441068475598671748611961484261) * 10 ^ 70 +
        4432265281635444583430758764129426587027184705859089933585719309850035) * 10 ^ 70 +
        5067763019371980922760278557288194268185140792953847572254197759710352) * 10 ^ 70 +
        4972017008269340326222026647302726750328927439014501987638091553410809) * 10 ^ 70 +
        0570341931767985793195524107906799129933604526238613932587138741220844) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 147 +
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
  rw [recurrence5Scalar1Exceptional_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_232 :
    recurrence5Scalar1Exceptional.coeff 232 =
      ((((((3829560 * 10 ^ 70 +
        5077653916831807215426236092145532363491186044570508625045056496913972) * 10 ^ 70 +
        2370947651738837601676874649847225371278784902817528011887547277542301) * 10 ^ 70 +
        8957315895475571381872101775446692297346397867277644869399911447077371) * 10 ^ 70 +
        3097148750711531491382552351497536557809990155677486833657998297084007) * 10 ^ 70 +
        9557012971334703775196144632282613917288846366896825887634869239304529) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 148 +
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
  rw [recurrence5Scalar1Exceptional_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_233 :
    recurrence5Scalar1Exceptional.coeff 233 =
      -((((((3635353 * 10 ^ 70 +
        8916619033523006510034528791618718863876165017796903517336943423747250) * 10 ^ 70 +
        2043007562862899187877476171823549802025338650549013919109017805353883) * 10 ^ 70 +
        4252196734423451287663387940391091997889352462654925089258704761756181) * 10 ^ 70 +
        2165320862213063342851253092453499786320636969147819035406252276237471) * 10 ^ 70 +
        6039331638307927050991597485197190012281021074262737832521223638588972) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 149 +
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
  rw [recurrence5Scalar1Exceptional_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_234 :
    recurrence5Scalar1Exceptional.coeff 234 =
      ((((((3267985 * 10 ^ 70 +
        1765911737660984663081473579212118162520308295191218882024603522298168) * 10 ^ 70 +
        1690967855370151284643932003985664976123001020037991167405957483457469) * 10 ^ 70 +
        0744719911866424025070170139602322453582538310928627913411059733179119) * 10 ^ 70 +
        3430633929886320221059397043972872051647893061708339081432039414164677) * 10 ^ 70 +
        1172822432655471972549531126462224109068775478551322356111362209208737) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 150 +
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
  rw [recurrence5Scalar1Exceptional_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_235 :
    recurrence5Scalar1Exceptional.coeff 235 =
      -((((((2783778 * 10 ^ 70 +
        5081144197036236197882392653692137407309060340514873371617583083764721) * 10 ^ 70 +
        2851897015453696677265247790203921147866632269489428439092689960277088) * 10 ^ 70 +
        7879553434645687887858797797064594518001186466318105185841962989045962) * 10 ^ 70 +
        1278477112651578935201982467651302981793956178653011815662526488681970) * 10 ^ 70 +
        7221409291994944218955051821193804288090484411112439877807170481777693) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 151 +
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
  rw [recurrence5Scalar1Exceptional_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_236 :
    recurrence5Scalar1Exceptional.coeff 236 =
      ((((((2239201 * 10 ^ 70 +
        7889024925154106295640289390638469006489524220841082130990551246039049) * 10 ^ 70 +
        2470822773260345148574105987023992991789435171239099985798513865332809) * 10 ^ 70 +
        0995603321871323760443510359877765926899533722428169348957681709439604) * 10 ^ 70 +
        1915558694160400686687375495601006788132172005032157942921547777071919) * 10 ^ 70 +
        9280318462606274650215852337330566841391239906208437347080229441301131) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 152 +
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
  rw [recurrence5Scalar1Exceptional_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_237 :
    recurrence5Scalar1Exceptional.coeff 237 =
      -((((((1685407 * 10 ^ 70 +
        3332988291438694844688022521353716982005620715225355812373691565584874) * 10 ^ 70 +
        8017607068780172859414718682097113659403714050356251200103351863941036) * 10 ^ 70 +
        6478808158762045998945339005636514231079893379116549224001077591465818) * 10 ^ 70 +
        4892321184398578615101493473369742141548457325575862216102891306510597) * 10 ^ 70 +
        5157252292804848156137465291066113465935037739502907239771763211972272) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 153 +
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
  rw [recurrence5Scalar1Exceptional_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_238 :
    recurrence5Scalar1Exceptional.coeff 238 =
      ((((((1164232 * 10 ^ 70 +
        3788455249276262375165593881734130588304697199454977359855168162006380) * 10 ^ 70 +
        1206149327349752765821611420980398923845056925956775025275475919966761) * 10 ^ 70 +
        5459869676828730191333267109587413315203060870529394692207816554370458) * 10 ^ 70 +
        3033817844205565232796678530211961250531137725808143020629632416504237) * 10 ^ 70 +
        1221664793671700836065029289554594381298255162107416047804899792355256) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 154 +
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
  rw [recurrence5Scalar1Exceptional_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_239 :
    recurrence5Scalar1Exceptional.coeff 239 =
      -((((((705930 * 10 ^ 70 +
        3374858829524705778747327654744756503527953361969013782666246119609631) * 10 ^ 70 +
        8611329434614252979506981531334608019508734195241915330640783692358060) * 10 ^ 70 +
        2012669914069177385399141836843089023351154975833628486646788201078554) * 10 ^ 70 +
        9480204119141214818194594887446654346197409978129826819701293036298453) * 10 ^ 70 +
        6230799734366034442550808494065853823455294009921443148576820640663908) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 155 +
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
  rw [recurrence5Scalar1Exceptional_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_240 :
    recurrence5Scalar1Exceptional.coeff 240 =
      ((((((328616 * 10 ^ 70 +
        0841302547426984786534439274146093956520760772012457572799658210208681) * 10 ^ 70 +
        1891780324267342280331532486194059613510137842580788413172680071319184) * 10 ^ 70 +
        2932461510584456070064433265780817322481312679766843783816358177412013) * 10 ^ 70 +
        7533927992178705271008992998260903765038161502677951766877219620123268) * 10 ^ 70 +
        1579465442529362028195616728051889512509055731163567420673382053872486) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 156 +
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
  rw [recurrence5Scalar1Exceptional_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_241 :
    recurrence5Scalar1Exceptional.coeff 241 =
      -((((((39171 * 10 ^ 70 +
        1154755726949945576138838116185298956093526239488799585712018801537962) * 10 ^ 70 +
        5251977772857705062895388473148258753400474400320378184158844070332967) * 10 ^ 70 +
        9625247956608466166423991628537481163825904587519260541938196272309451) * 10 ^ 70 +
        8278859662860581336163136455903157158540399072793619605639161796774150) * 10 ^ 70 +
        6922344638597171400612091703915078606148356183908879604704058681743215) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 157 +
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
  rw [recurrence5Scalar1Exceptional_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_242 :
    recurrence5Scalar1Exceptional.coeff 242 =
      -((((((164801 * 10 ^ 70 +
        1582433025580855327204271281937665045938827125356892206371092377802979) * 10 ^ 70 +
        6119763998649072588039323703913445738183352046296180584208832242394968) * 10 ^ 70 +
        1280679803656641436806357494245671468976446713013225999522352252139033) * 10 ^ 70 +
        4226229315924833360337711417860096175749680912352649027163971381469754) * 10 ^ 70 +
        6842330959621040291024243470810614144760818553726232367761957851788655) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 158 +
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
  rw [recurrence5Scalar1Exceptional_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_243 :
    recurrence5Scalar1Exceptional.coeff 243 =
      ((((((292442 * 10 ^ 70 +
        1472953507722844783067324220702395498710833253521393797950881391378352) * 10 ^ 70 +
        0501449304217343700190103835952212281301754872386661138776382194374966) * 10 ^ 70 +
        0157150490289719017650346706545645072155386243915449431471519886786717) * 10 ^ 70 +
        3351727589049653590113481195383891905632340084175138555033801942060246) * 10 ^ 70 +
        4770280486513702988964526500507596491960823488463587121631507185337611) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 159 +
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
  rw [recurrence5Scalar1Exceptional_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_244 :
    recurrence5Scalar1Exceptional.coeff 244 =
      -((((((356976 * 10 ^ 70 +
        1227688542498022471067402966710655917361723661574020100901597112681015) * 10 ^ 70 +
        0457375589402725973773695854699621869853217050204487771793127379831957) * 10 ^ 70 +
        9507405755425833465764884192039404519822556845513211586631565639859334) * 10 ^ 70 +
        3828782527283959848911918222907688559830550552663295533442315950927193) * 10 ^ 70 +
        7100910685283667703079298803996001293398279637943908153147345230291331) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 160 +
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
  rw [recurrence5Scalar1Exceptional_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_245 :
    recurrence5Scalar1Exceptional.coeff 245 =
      ((((((373282 * 10 ^ 70 +
        4306918802713110990236531752192648888727557826126175135412399527817050) * 10 ^ 70 +
        0239478855262291495889251692517924000877007951020304751468423800216398) * 10 ^ 70 +
        5500547096147027183572988695573394996295032287105513123161264129855986) * 10 ^ 70 +
        4650918145462250339460586765436504595412361340613335836851826035284654) * 10 ^ 70 +
        2741314762598207211777005790438831933306393251958889418688434888165470) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 161 +
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
  rw [recurrence5Scalar1Exceptional_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_246 :
    recurrence5Scalar1Exceptional.coeff 246 =
      -((((((355943 * 10 ^ 70 +
        3882687568030657150947270178436796961844041091952736448390625727968387) * 10 ^ 70 +
        9573919350115410963973293357338303715718589719353582034041892761162820) * 10 ^ 70 +
        4900158555302034612692535793596000270683502832054976857088227010483717) * 10 ^ 70 +
        5465958024920052568472009873425794439856952274648610383906482125901386) * 10 ^ 70 +
        9753663440015268134100226610936119038474306454008025505219271784621290) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 162 +
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
  rw [recurrence5Scalar1Exceptional_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_247 :
    recurrence5Scalar1Exceptional.coeff 247 =
      ((((((317881 * 10 ^ 70 +
        4418117247195145634105225757703114961161535558982798872750755828176065) * 10 ^ 70 +
        0396786052639261403215803386903309485046421108011507485608501930531233) * 10 ^ 70 +
        4257032754553571959609729711729590926955108873995016915312697186428512) * 10 ^ 70 +
        8729653487777898183829263366788960116283771065246673724648542451442420) * 10 ^ 70 +
        1020489324499120661084209318505659105758590810517581178927128698682039) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 163 +
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
  rw [recurrence5Scalar1Exceptional_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_248 :
    recurrence5Scalar1Exceptional.coeff 248 =
      -((((((269587 * 10 ^ 70 +
        4021053451563221754437296440312479739548986688181572636192127763099593) * 10 ^ 70 +
        5865827963202236498271839221449209095404260651537471850160194883895171) * 10 ^ 70 +
        2772141979384197147277626890267006094918075325192823084187529440801463) * 10 ^ 70 +
        5946332019766737150619523118644086340764086180725380578102426590016192) * 10 ^ 70 +
        9384390378419026845815635167609219519625501817010103798146467241118713) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 164 +
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
  rw [recurrence5Scalar1Exceptional_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_249 :
    recurrence5Scalar1Exceptional.coeff 249 =
      ((((((218860 * 10 ^ 70 +
        0741775966083347273060521287593520274906002264150704165397550253919842) * 10 ^ 70 +
        8627172660209238023075581135157188235334513652197396414349523305483061) * 10 ^ 70 +
        9116202412719314161066785754122348342922295975077047292842734597252279) * 10 ^ 70 +
        9463631320150629394833582940567466927880371709113783732068964320143643) * 10 ^ 70 +
        3755348382638131135159886178346572017922670224810593561958579494552728) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 165 +
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
  rw [recurrence5Scalar1Exceptional_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_250 :
    recurrence5Scalar1Exceptional.coeff 250 =
      -((((((170931 * 10 ^ 70 +
        3508723391467162176730320802131676491103145715916726638327140716831575) * 10 ^ 70 +
        6975664401997080109802730069712544415550602702587696198599921512713453) * 10 ^ 70 +
        5803655397145911792752094438864373668687090833627253442599494794180533) * 10 ^ 70 +
        3408365871004667851138305359991691391730838290258969760028540590113146) * 10 ^ 70 +
        7654186201634678004020948582900761272555621407086025630071180485962839) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 166 +
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
  rw [recurrence5Scalar1Exceptional_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_251 :
    recurrence5Scalar1Exceptional.coeff 251 =
      ((((((128837 * 10 ^ 70 +
        2200488560630454627895815571751105610857605496630978037187386745642432) * 10 ^ 70 +
        7479655338905547619441819345597979403376674596085089739635845342194694) * 10 ^ 70 +
        6630297072853009992719567174829190394481038673025782787879117697912585) * 10 ^ 70 +
        2386111165083330941785846873932042638362155149246766802031966597749041) * 10 ^ 70 +
        9762633918702177651289614784516616975917495298995000333214679649002403) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 167 +
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
  rw [recurrence5Scalar1Exceptional_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_252 :
    recurrence5Scalar1Exceptional.coeff 252 =
      -((((((93906 * 10 ^ 70 +
        5503896262835393815990375275142383655734640889323310234380388679910979) * 10 ^ 70 +
        8628345666634559954091394764923281659469381330686776703555858427735571) * 10 ^ 70 +
        8897209254096097080670960695593447521752826520728303137667950115295082) * 10 ^ 70 +
        4590118896357020476936098980523570708151061970872815865840358387007404) * 10 ^ 70 +
        8084448359151785053837845821380012319214531555362465749955557350310940) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 168 +
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
  rw [recurrence5Scalar1Exceptional_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_253 :
    recurrence5Scalar1Exceptional.coeff 253 =
      ((((((66266 * 10 ^ 70 +
        2981978818252643086512728246560814299181731020246835067067979922006009) * 10 ^ 70 +
        8335149228784719653109499418310576641232806783139614271458841929175636) * 10 ^ 70 +
        8148153492452083393748183146516163789692813659408895630740325005637562) * 10 ^ 70 +
        4309896133369146070092556928253952760713661587656431863685931630745545) * 10 ^ 70 +
        0416121778604959332759732683761822969524356334526404111817827572016047) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 169 +
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
  rw [recurrence5Scalar1Exceptional_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_254 :
    recurrence5Scalar1Exceptional.coeff 254 =
      -((((((45294 * 10 ^ 70 +
        6154621772248728720518031078058755777434861780321099004727963741632418) * 10 ^ 70 +
        5803905045138885397849210069554686341103528384032222085748680021775897) * 10 ^ 70 +
        4535711543629627251250242466179776384839495674902087464691243494963022) * 10 ^ 70 +
        2545356499868134882679621434809366622950334498920448590964709521934134) * 10 ^ 70 +
        3682818451771172629378902951454118349310213262288301737420857156233799) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 170 +
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
  rw [recurrence5Scalar1Exceptional_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_255 :
    recurrence5Scalar1Exceptional.coeff 255 =
      ((((((29984 * 10 ^ 70 +
        9255071226311741139002154176236716709379595551065375218435014576036188) * 10 ^ 70 +
        5252539619869275986048220251297073182499351932142670982265700029174429) * 10 ^ 70 +
        6808059468237828287704410465778027013988084046910858594148153922471034) * 10 ^ 70 +
        4144514148533557873448569352870148365806506392900529220591231270864690) * 10 ^ 70 +
        1158743133693240284774897678949937512281429507779139310441260979051325) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 171 +
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
  rw [recurrence5Scalar1Exceptional_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_256 :
    recurrence5Scalar1Exceptional.coeff 256 =
      -((((((19209 * 10 ^ 70 +
        7472089996566949740003437199959910541957805005452895711987775417398672) * 10 ^ 70 +
        3652429957500067681282593895603868498517360250180469396322626617960270) * 10 ^ 70 +
        6550020909100480472956930463412555005123983120293865823905431792543323) * 10 ^ 70 +
        9040873707424566835701317888112775526719675754054179436042331722651019) * 10 ^ 70 +
        0243963741732372861646900547211026531296378724171166825502545020691053) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 172 +
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
  rw [recurrence5Scalar1Exceptional_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_257 :
    recurrence5Scalar1Exceptional.coeff 257 =
      ((((((11890 * 10 ^ 70 +
        9014737141742737322542800283777705762794002225464688676080613134197712) * 10 ^ 70 +
        7065116402469489125838157707307458065129868852508781242632723471756504) * 10 ^ 70 +
        6591768478046350063763424533050352269816373495118544320905766536097009) * 10 ^ 70 +
        5714565207867316126840721833691437527668015930207049816720402902651271) * 10 ^ 70 +
        0194118046887249053025283684024934243326171950231648260329762063272010) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 173 +
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
  rw [recurrence5Scalar1Exceptional_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_258 :
    recurrence5Scalar1Exceptional.coeff 258 =
      -((((((7092 * 10 ^ 70 +
        8026221932374916028541447385104588622372902192143964940204465129991537) * 10 ^ 70 +
        6198764413442224548432353547909497235624475812173119742196097720433274) * 10 ^ 70 +
        2109992668978467740969069510761462633790930904033385096071998975933460) * 10 ^ 70 +
        4801569539369415820658032491588307268051614994758502508390477326718771) * 10 ^ 70 +
        9788012565447177214242750104969526703701916355094027704612313643215750) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 174 +
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
  rw [recurrence5Scalar1Exceptional_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_259 :
    recurrence5Scalar1Exceptional.coeff 259 =
      ((((((4059 * 10 ^ 70 +
        2021657652723947806282968422565303461690731259613313270834260556280323) * 10 ^ 70 +
        7755269734657953075445271696143288514761212740669289751018255982466542) * 10 ^ 70 +
        2175050108880972457859159029619879335145052762414434595883406190493647) * 10 ^ 70 +
        0009802776096012342841414934485938615105093981289308105346505180275873) * 10 ^ 70 +
        0283596738540146962486752245962606880277553605004981621256562609416281) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 175 +
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
  rw [recurrence5Scalar1Exceptional_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_260 :
    recurrence5Scalar1Exceptional.coeff 260 =
      -((((((2212 * 10 ^ 70 +
        9539559362218792253374849307378567422529343921736455684234201339275636) * 10 ^ 70 +
        0581199167662156892457036573838257230085947612221354343375275111480094) * 10 ^ 70 +
        1146753986107769971776683224331867876245006667074926563390986555483850) * 10 ^ 70 +
        0614749263790380503537627066083303996616257666263210268519277991779899) * 10 ^ 70 +
        1085984849764917946831388773069191873185579398528939362263595260923172) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 176 +
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
  rw [recurrence5Scalar1Exceptional_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_261 :
    recurrence5Scalar1Exceptional.coeff 261 =
      ((((((1135 * 10 ^ 70 +
        0397198693339505635532334099565465400927127824625649690721225902737068) * 10 ^ 70 +
        3218084412583366337524735982544048027133154798691952468917715333827506) * 10 ^ 70 +
        1050335571108000630767952877539131120208757089110912722649212042859481) * 10 ^ 70 +
        6364554869325413300407446092644469285400126868086504512807745956992436) * 10 ^ 70 +
        7840160628608632893300048340191597355252712063661234548778799582042245) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 177 +
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
  rw [recurrence5Scalar1Exceptional_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_262 :
    recurrence5Scalar1Exceptional.coeff 262 =
      -((((((534 * 10 ^ 70 +
        8086178775320463441093597750703941694072287215122527570973310185022307) * 10 ^ 70 +
        6754993181287410136913347383090226422063916197362830519203079294716174) * 10 ^ 70 +
        9151335612833162618024887677688022695069859204759074658289852517904533) * 10 ^ 70 +
        9343802336035014135197498860804147074941556275285810359329175739927424) * 10 ^ 70 +
        6005540770470325093267061683776296074602319366249517317125562499600499) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 178 +
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
  rw [recurrence5Scalar1Exceptional_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_263 :
    recurrence5Scalar1Exceptional.coeff 263 =
      ((((((219 * 10 ^ 70 +
        2242189000925969300768437083919741096827516364751007437579401557962488) * 10 ^ 70 +
        0323925471506156230766753432172516058633219356940865410015229423630816) * 10 ^ 70 +
        6483611122966631745613650788778662152218138446483778911136832729312981) * 10 ^ 70 +
        0149268416802956070044257347138239943846192323547106606542505516646502) * 10 ^ 70 +
        8648675642091872108061136345309643961918302112438685864032035501891506) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 179 +
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
  rw [recurrence5Scalar1Exceptional_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_264 :
    recurrence5Scalar1Exceptional.coeff 264 =
      -((((((65 * 10 ^ 70 +
        4749323635496771801637841235646253386824837891901236377516776190146719) * 10 ^ 70 +
        5848646189659557298917107681924786367204460707513137529586560440977676) * 10 ^ 70 +
        7987635295708023702530757788838004551571746546544159724014406926054648) * 10 ^ 70 +
        9238916233046339147114152478404822699706804670792389064115835599257276) * 10 ^ 70 +
        5035768958616531507637288796471477508743400427601005441722263548074449) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 180 +
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
  rw [recurrence5Scalar1Exceptional_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_265 :
    recurrence5Scalar1Exceptional.coeff 265 =
      -((((((1 * 10 ^ 70 +
        1957898748089028024189174558454920562271975339828751884545937864844224) * 10 ^ 70 +
        3833961609401158846507397822857557031894046471525853239241694143198899) * 10 ^ 70 +
        4489377525793824846975786053297232990412873503326344189648128788327711) * 10 ^ 70 +
        0513876058347290612489711644488714274890548976967433925077785165118222) * 10 ^ 70 +
        2702627083183942093679869305064950843401651884220360513995245695276235) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 181 +
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
  rw [recurrence5Scalar1Exceptional_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_266 :
    recurrence5Scalar1Exceptional.coeff 266 =
      ((((((24 * 10 ^ 70 +
        1836845903267623227400969815720682342783810480132060574900664977183834) * 10 ^ 70 +
        2928160032582131692541361181756650556783052749383741314094121701169208) * 10 ^ 70 +
        5979728551125591419431459795391759078271541600967392935499312630335933) * 10 ^ 70 +
        9133564692309094582157635084825465083571046754422726410429735549085366) * 10 ^ 70 +
        8272574046372281152100151312143131842347106182378494436446478375314123) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 182 +
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
  rw [recurrence5Scalar1Exceptional_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_267 :
    recurrence5Scalar1Exceptional.coeff 267 =
      -((((((27 * 10 ^ 70 +
        3588001505581563515093118141768193471744178833987000242351664897151983) * 10 ^ 70 +
        2228862819787576118973937045606686869416885929846154261089786090032141) * 10 ^ 70 +
        7732207763469691616891042563631925839676011364258884686655002062172375) * 10 ^ 70 +
        9423719281278844772648753893235960775602232104596964477778436513966666) * 10 ^ 70 +
        6602641919187081849191903013520728537500403143054494781196868945420139) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 183 +
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
  rw [recurrence5Scalar1Exceptional_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_268 :
    recurrence5Scalar1Exceptional.coeff 268 =
      ((((((23 * 10 ^ 70 +
        0141386949395964285768701700863134975236658497593074130940188099011743) * 10 ^ 70 +
        9763403050670771295841324122239687634976466015686965772356100728640083) * 10 ^ 70 +
        0358928525840706184249998461213517782497930989606882851083542003079344) * 10 ^ 70 +
        4678037924081703956862198865683318608018743446404622338784584542912177) * 10 ^ 70 +
        4767202132554330597702360996510304401027570426821602355064792047810050) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 184 +
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
  rw [recurrence5Scalar1Exceptional_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_269 :
    recurrence5Scalar1Exceptional.coeff 269 =
      -((((((16 * 10 ^ 70 +
        9369627936354551210884986372108710324485914122385426916309815746203774) * 10 ^ 70 +
        4460343781931277596425620445039678785569519521715603349713975036033553) * 10 ^ 70 +
        3032331492801465702697939616269176648360368651242646370423005504642668) * 10 ^ 70 +
        1838021465214052984831178448823326260162521595692770084141879707905784) * 10 ^ 70 +
        8842866751855529480826796624573200274878786892148425364523310457763545) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 185 +
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
  rw [recurrence5Scalar1Exceptional_coeff_269_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_270 :
    recurrence5Scalar1Exceptional.coeff 270 =
      ((((((11 * 10 ^ 70 +
        4823094025117643065082564325156064733177684308888974732000633478621190) * 10 ^ 70 +
        7428874021849330869670372502653786174155776053462554150460826316793843) * 10 ^ 70 +
        5366408979789016214101155024354097017632353719265359288557480925352216) * 10 ^ 70 +
        2528761499011563157437278970691176514109598368737409726168824176198766) * 10 ^ 70 +
        8515680659698796385553259879512649948965508693695679376362031072324027) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 186 +
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
  rw [recurrence5Scalar1Exceptional_coeff_270_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_271 :
    recurrence5Scalar1Exceptional.coeff 271 =
      -((((((7 * 10 ^ 70 +
        3370869028932396466660811344410914564326595878895853207836175319347154) * 10 ^ 70 +
        9609637465957278243670096416648973854827030626987211298490007699192787) * 10 ^ 70 +
        4413332527048533033426137554046006110016842310263852654062333095942759) * 10 ^ 70 +
        9411742701951702990095230480706130814820768842648198875333369733298578) * 10 ^ 70 +
        3568301691603723118057631733261568738858336271400266764867442678014919) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 187 +
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
  rw [recurrence5Scalar1Exceptional_coeff_271_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_272 :
    recurrence5Scalar1Exceptional.coeff 272 =
      ((((((4 * 10 ^ 70 +
        4720332264816964192065356216236757816007398563135438307980708956112722) * 10 ^ 70 +
        6746449849930212737406251258914010947560818055514757952153578918144872) * 10 ^ 70 +
        0526860478748263771999432525628659588647426033818873867536939425910488) * 10 ^ 70 +
        1164224483675356961526737363755437219875357992712393686927887903422118) * 10 ^ 70 +
        1812855199413624721940823257946991756316660259384892632287030955875615) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 188 +
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
  rw [recurrence5Scalar1Exceptional_coeff_272_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_273 :
    recurrence5Scalar1Exceptional.coeff 273 =
      -((((((2 * 10 ^ 70 +
        6175104730107535720520755894214407439813485192772151273298547864996565) * 10 ^ 70 +
        7760031638266301278632091031119842568576421200399884573622187739032286) * 10 ^ 70 +
        9712077890579057692318286104311159603785274331505588069219567699154783) * 10 ^ 70 +
        5512801871843421002381646339185248735770064297838534139054740901138284) * 10 ^ 70 +
        5595950989457369628032568110193877882261606169439623734926553290504984) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 189 +
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
  rw [recurrence5Scalar1Exceptional_coeff_273_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_274 :
    recurrence5Scalar1Exceptional.coeff 274 =
      ((((((1 * 10 ^ 70 +
        4767449745963351080625226494237786030998390345517638785685098955306460) * 10 ^ 70 +
        7334835102547335367361879401405937250394517917193071059001857401680091) * 10 ^ 70 +
        7795474236894677545533867878985093341989271236626791625229100659252837) * 10 ^ 70 +
        6359318319076978122068973855402797638541860532939251249599976214726534) * 10 ^ 70 +
        7244092927762699276587881220999548568383113176486716849698088308959263) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 190 +
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
  rw [recurrence5Scalar1Exceptional_coeff_274_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_275 :
    recurrence5Scalar1Exceptional.coeff 275 =
      -(((((8045041667490213510178161673938450699173296288088701984395401489991266 * 10 ^ 70 +
        3150771734966170959961150927881048069550145686914093792994886979115567) * 10 ^ 70 +
        3351723349733862164272226327832453226254801924349956057373279204027502) * 10 ^ 70 +
        7195649368826029833428577958454173665799532366964878128587717121814170) * 10 ^ 70 +
        4005080266161076947242024405919109660680329131834215403435676621391967) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 191 +
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
  rw [recurrence5Scalar1Exceptional_coeff_275_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_276 :
    recurrence5Scalar1Exceptional.coeff 276 =
      (((((4232764377489492211065626064960965194754972853586739243734614015123462 * 10 ^ 70 +
        8107304243348683327986880499498204159749428480727974332267679378186544) * 10 ^ 70 +
        3346599744815511729120415054956065940674353877001527004061077497604244) * 10 ^ 70 +
        9203767923443136194473705199879927969338734758391421821576122226475142) * 10 ^ 70 +
        9759424994808820847377602576722066189023527459801223119272827500567005) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 192 +
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
  rw [recurrence5Scalar1Exceptional_coeff_276_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_277 :
    recurrence5Scalar1Exceptional.coeff 277 =
      -(((((2147475350649081650753907225537177570759468791417264702984905814099723 * 10 ^ 70 +
        3003396179774505140695947832469684542783299821248147254747715679486550) * 10 ^ 70 +
        6050974284436164732217905297520742016279438738132636825315338840209901) * 10 ^ 70 +
        2957923954771713319525818231741285748793035941939709564835085167407851) * 10 ^ 70 +
        5553846318718171291394071140227343803501427285904562942676040396283334) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 193 +
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
  rw [recurrence5Scalar1Exceptional_coeff_277_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_278 :
    recurrence5Scalar1Exceptional.coeff 278 =
      (((((1046682268542196117924595217309219206189984564540982366119470044603012 * 10 ^ 70 +
        6895991325139863025467523036707816616041101278047561656925687970086550) * 10 ^ 70 +
        5668475096419847036714751237929404444756850647787098564927088616368223) * 10 ^ 70 +
        0890447659655187834059177985678012052522128828257970885469935052109567) * 10 ^ 70 +
        4669246291587760120194656571445759408133891153887302156717932919849555) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 194 +
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
  rw [recurrence5Scalar1Exceptional_coeff_278_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_279 :
    recurrence5Scalar1Exceptional.coeff 279 =
      -(((((486539963082342125800698307324133084806393126904560474851313162752593 * 10 ^ 70 +
        2763124419417293366510538119500433159349007022227678179319544541960757) * 10 ^ 70 +
        2796903855018438469851661359986743990883266921416991059194297790634216) * 10 ^ 70 +
        3356787291709752935307176161012612891237318781872783359614587633505898) * 10 ^ 70 +
        6492505524916892875583722518292859434415606796169833785287747051868050) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 195 +
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
  rw [recurrence5Scalar1Exceptional_coeff_279_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_280 :
    recurrence5Scalar1Exceptional.coeff 280 =
      (((((212688930241249563739193988811859202760477107401345429036845316432826 * 10 ^ 70 +
        4179162528218744732225540978982643029967709134412847175449446537924344) * 10 ^ 70 +
        9764089333238347578979835376363644285200385351551209654964739848103646) * 10 ^ 70 +
        1960529349911265781461269941764707009544078463349841621283971563669551) * 10 ^ 70 +
        7992233854785749020916487326784684215001431014367144730512640722036973) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 196 +
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
  rw [recurrence5Scalar1Exceptional_coeff_280_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_281 :
    recurrence5Scalar1Exceptional.coeff 281 =
      -(((((84901029891489378939380702062853600946526961337019338943677746804534 * 10 ^ 70 +
        4830385410303499369052317557785249910030649157710323831131187591012980) * 10 ^ 70 +
        2631364656256200314592867529734935623779056469879633876302546155933773) * 10 ^ 70 +
        2935755682176957773945110720687797989597434849617790625272230915954740) * 10 ^ 70 +
        4182732919260185740850547953507092941269324546007281289629320946017958) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 197 +
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
  rw [recurrence5Scalar1Exceptional_coeff_281_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_282 :
    recurrence5Scalar1Exceptional.coeff 282 =
      (((((28705698740785025858245603165447691529088569428657665043690495738335 * 10 ^ 70 +
        1356685633645687549811361622240910231392957584379909130258016075678108) * 10 ^ 70 +
        6459820458206260613909408346748860493643529788577323216304612198135709) * 10 ^ 70 +
        4035566549840818283869143945517388138827446341263975148999404352421667) * 10 ^ 70 +
        7592790178281222275301140378676928844449543815507004499787713066685275) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 198 +
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
  rw [recurrence5Scalar1Exceptional_coeff_282_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_283 :
    recurrence5Scalar1Exceptional.coeff 283 =
      -(((((6022374278649168120339232806596000081262790777889267964458656025500 * 10 ^ 70 +
        8313454653617635256898094184220164020414485764420722379621430257583931) * 10 ^ 70 +
        7429724702239508909344549442301690253301312091324591156348287979521219) * 10 ^ 70 +
        1747243848510365833231136508437639908909177204885988186857924110909420) * 10 ^ 70 +
        0623909433542823746342279740453118638807175998623278306752043604424593) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 199 +
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
  rw [recurrence5Scalar1Exceptional_coeff_283_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_284 :
    recurrence5Scalar1Exceptional.coeff 284 =
      -(((((1852163455161984163280125472938642803079042310070309235897372228533 * 10 ^ 70 +
        1581874846022352448001966224663867320095860765948126870794395019364899) * 10 ^ 70 +
        7223960210001551332644139565767352827082745798343452947143788201249708) * 10 ^ 70 +
        6697775341862840688869358461996937397308430698991839695213547228225415) * 10 ^ 70 +
        4674301179199065367523622569760174603560476992561259181837079377999620) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 200 +
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
  rw [recurrence5Scalar1Exceptional_coeff_284_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_285 :
    recurrence5Scalar1Exceptional.coeff 285 =
      (((((3693637067682904626111906889478587591999056280827659936365524522258 * 10 ^ 70 +
        1540098719005879519857711619037634845709986866156190304779741852157863) * 10 ^ 70 +
        8683515103973782354829053251643434920798064270611525799897663169474362) * 10 ^ 70 +
        9619978710071805435068896538867639620301194657709231527766577532106353) * 10 ^ 70 +
        8778934054502734760666919550092353173408314554714310487257387306691425) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 201 +
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
  rw [recurrence5Scalar1Exceptional_coeff_285_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_286 :
    recurrence5Scalar1Exceptional.coeff 286 =
      -(((((3394589826893880931385844918201701369304427316114911129248043648523 * 10 ^ 70 +
        2956870111566660348513292488466306286121247828624857388588179754006109) * 10 ^ 70 +
        2885700779780819381917114632999464691775673744055329445104227241302436) * 10 ^ 70 +
        5295178733148270103049424199403822275986498371078626863526845351910991) * 10 ^ 70 +
        4947265527293691352219592496065433849160987395534489522161966103779932) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 202 +
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
  rw [recurrence5Scalar1Exceptional_coeff_286_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_287 :
    recurrence5Scalar1Exceptional.coeff 287 =
      (((((2552651656042288911913626903492653142487292619836041113299420120860 * 10 ^ 70 +
        3459095608679969814093149746281439272724718702236635568319663488225517) * 10 ^ 70 +
        1112102175789662439534806255319119140844806357955002003904597224012620) * 10 ^ 70 +
        2765665834409690771010773327073296878804319877531029405781168097334262) * 10 ^ 70 +
        9676416828863014601446192690973367144517691326334620529612192115891984) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 203 +
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
  rw [recurrence5Scalar1Exceptional_coeff_287_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_288 :
    recurrence5Scalar1Exceptional.coeff 288 =
      -(((((1744842985629965263077718833707054745868269654756721895177789069576 * 10 ^ 70 +
        6054545324740770901321466768500031805935726140707636476889309687278993) * 10 ^ 70 +
        9099618025115738578561655544257120757069059559665824501787708963674509) * 10 ^ 70 +
        3353138680721590481685941854095770539944636744581093092489613287340794) * 10 ^ 70 +
        3494156124917334604008852352651865207262206452123292418769826190635524) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 204 +
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
  rw [recurrence5Scalar1Exceptional_coeff_288_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_289 :
    recurrence5Scalar1Exceptional.coeff 289 =
      (((((1126920359717776092364791829531483248474718526965067897516993229654 * 10 ^ 70 +
        8684478484624365037398148017428237455384110387328935815501369157361933) * 10 ^ 70 +
        9596426036535089309006058964485147932482643091074866566990528172530912) * 10 ^ 70 +
        4480160271884543329528727430294746508342398700844612833061562549845964) * 10 ^ 70 +
        3961639848524069796190938584689523677158119589591294162729982021745865) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 205 +
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
  rw [recurrence5Scalar1Exceptional_coeff_289_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_290 :
    recurrence5Scalar1Exceptional.coeff 290 =
      -(((((700309192372967424136672233668596061520603581378535395712778140688 * 10 ^ 70 +
        7832341333447232482448271909699579227739080229591843277271226223708087) * 10 ^ 70 +
        5284400362513471125290383369355902725445893270972301658142091343596365) * 10 ^ 70 +
        5446978716636706048735404174401226123219728929939586468398424690598361) * 10 ^ 70 +
        2575155494576906377897728705678368376299277254557526938235151729048378) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 206 +
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
  rw [recurrence5Scalar1Exceptional_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_291 :
    recurrence5Scalar1Exceptional.coeff 291 =
      (((((422707146352813457411582646968096183697211226477430331882083764254 * 10 ^ 70 +
        9337503952098291278463034261669348912304826526759564937128222927800012) * 10 ^ 70 +
        2514621042369659455541850040969991324892991584949653239100000551032585) * 10 ^ 70 +
        2331468147811496301997110272561835302699456361579837548016998502684576) * 10 ^ 70 +
        7752910578909472744544768365520437630627743445723237960947758731540888) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 207 +
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
  rw [recurrence5Scalar1Exceptional_coeff_291_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_292 :
    recurrence5Scalar1Exceptional.coeff 292 =
      -(((((249048945321933622904556455401838952274574021792027803641952813584 * 10 ^ 70 +
        3919074639826473508712642455837494137323624127147576778022018436774995) * 10 ^ 70 +
        4432461278563538121114712525681140840392733120941101742690548897025396) * 10 ^ 70 +
        5593354577023353626213104192216549118349793175869324310403292580631378) * 10 ^ 70 +
        6989723383842340470707088755665653067885681016226597425824901685761337) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 208 +
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
  rw [recurrence5Scalar1Exceptional_coeff_292_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_293 :
    recurrence5Scalar1Exceptional.coeff 293 =
      (((((143559295241178716370997752070255028645579608029687877579766515455 * 10 ^ 70 +
        4123373848104207071975371634984410716775591876670222323660530190956839) * 10 ^ 70 +
        4327184145513201354649590782452396100650721028930607159262132007631968) * 10 ^ 70 +
        8819589628282459528098580383244897049302565896941533718708334654212803) * 10 ^ 70 +
        9163510660564756118876124273526121541621921283438039440547269088102890) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 209 +
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
  rw [recurrence5Scalar1Exceptional_coeff_293_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_294 :
    recurrence5Scalar1Exceptional.coeff 294 =
      -(((((81014700941398686643115076613041978651450120580342159917332032180 * 10 ^ 70 +
        0370382678512783664551595261287690140700359718705244672839710980164035) * 10 ^ 70 +
        7762546155515291028567676570685775849992919032167966498488629176119500) * 10 ^ 70 +
        3146721806944048961182190205710584794168438812003452109083248083617652) * 10 ^ 70 +
        9043848889582829359687665604977135956090649868973871388125385474992732) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 210 +
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
  rw [recurrence5Scalar1Exceptional_coeff_294_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_295 :
    recurrence5Scalar1Exceptional.coeff 295 =
      (((((44737214888195433375844382558115462062682923888655022167414437531 * 10 ^ 70 +
        0935751859280249778838443829633444202315430105785229696226875018002561) * 10 ^ 70 +
        2618716182273658297763613110334852884867946697612419821994049685995974) * 10 ^ 70 +
        1451367218476107758355856440749551340318179549082223020766205095126112) * 10 ^ 70 +
        0804111138444916056897702076342592855373514077521728565032971727454546) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 211 +
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
  rw [recurrence5Scalar1Exceptional_coeff_295_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_296 :
    recurrence5Scalar1Exceptional.coeff 296 =
      -(((((24140551260659466405337096351251385689697611674696638167616187971 * 10 ^ 70 +
        1401085163227175466445142408849679077350301517704560643886784303812691) * 10 ^ 70 +
        0799002680067595931720609489538323560395937328456419995400178413676829) * 10 ^ 70 +
        2325681194511401533278140641829371904110064150221513137209589427535932) * 10 ^ 70 +
        9254179273361564490275066434076060081194012127072667435388937898450436) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 212 +
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
  rw [recurrence5Scalar1Exceptional_coeff_296_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_297 :
    recurrence5Scalar1Exceptional.coeff 297 =
      (((((12701029380673908567340318717811883335552741738803266146585792709 * 10 ^ 70 +
        6848670174466895841101786219066782354350306127706484983122767042514293) * 10 ^ 70 +
        6322087126892743335296869724536637655365059946829988344770975955904354) * 10 ^ 70 +
        3298909839348158388245384374131700414363095487613922420176821893695061) * 10 ^ 70 +
        4545420130486502578921451535925669249402978402047671848320560395201852) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 213 +
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
  rw [recurrence5Scalar1Exceptional_coeff_297_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_298 :
    recurrence5Scalar1Exceptional.coeff 298 =
      -(((((6494772724580509527742592353082935289915772905786959960219937961 * 10 ^ 70 +
        8608797602064270489052636137023950231252787459239300039381675084005294) * 10 ^ 70 +
        7781038551764243150128850985774774422262587541289631942171266838421099) * 10 ^ 70 +
        9067024890466019149203546685338580655635732625283100370640172463147339) * 10 ^ 70 +
        7598986458905817798780799306024987754938297986479729621983175440181276) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 214 +
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
  rw [recurrence5Scalar1Exceptional_coeff_298_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_299 :
    recurrence5Scalar1Exceptional.coeff 299 =
      (((((3213250764829968046303606268714000685622917332212059002935039025 * 10 ^ 70 +
        7257411597474384635868948691675217767750697218450111591553029749236118) * 10 ^ 70 +
        9738368156292703929615596255663682869539665886222457038736907902230865) * 10 ^ 70 +
        8256337168346305998384588870926225020671898611844664778584250760250163) * 10 ^ 70 +
        9241767588319661745614816469660641259873603203841019037954929873133280) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 215 +
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
  rw [recurrence5Scalar1Exceptional_coeff_299_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_300 :
    recurrence5Scalar1Exceptional.coeff 300 =
      -(((((1527658688003420857396102851302646980041534524140732852748088066 * 10 ^ 70 +
        7456067226664367248968407320298101519470427734906843760450035597844835) * 10 ^ 70 +
        7154133602038056762808501739860741979257701895911563205278602784430447) * 10 ^ 70 +
        4223438796688683235554895447694705321303637468065991743135968022061865) * 10 ^ 70 +
        1138381549009354223871372110868194939718936149937837050473593621753199) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 216 +
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
  rw [recurrence5Scalar1Exceptional_coeff_300_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_301 :
    recurrence5Scalar1Exceptional.coeff 301 =
      (((((690346564080703499814216122451484325990890555578340415086519979 * 10 ^ 70 +
        9471972765221721620494446042377108532024182861069311695846941722825528) * 10 ^ 70 +
        1555585622779707058423040089878698936593354629799288886961095387707166) * 10 ^ 70 +
        2054292450408563243275198492374003991463147301977902782835682919281226) * 10 ^ 70 +
        9303339334298708527779693940301218021832543554503778290107474945549712) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 217 +
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
  rw [recurrence5Scalar1Exceptional_coeff_301_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_302 :
    recurrence5Scalar1Exceptional.coeff 302 =
      -(((((290819452319497025838076509066354566015313999126408685221050628 * 10 ^ 70 +
        5112531292258470156009028610321922144746973905391207808138443454046253) * 10 ^ 70 +
        4892149571846710792181562964592315499141038451003161908773100533375094) * 10 ^ 70 +
        8200196507877484488819867656015115765710838878581223339882229990042445) * 10 ^ 70 +
        5790892151414085068480459836594089857900722213615561786543393938281586) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 218 +
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
  rw [recurrence5Scalar1Exceptional_coeff_302_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_303 :
    recurrence5Scalar1Exceptional.coeff 303 =
      (((((109672142904181138309257819685256655756962377484509594090786395 * 10 ^ 70 +
        6395176052588623273330154571244951004076604080146179863221763767551272) * 10 ^ 70 +
        6361954484347247885033984893482923637481066757577225642026146699806988) * 10 ^ 70 +
        3992341427747413441936691158602303676782572216256110475770695230253539) * 10 ^ 70 +
        5345658903576518752210917277357567523905401800620723674662094502010083) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 219 +
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
  rw [recurrence5Scalar1Exceptional_coeff_303_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_304 :
    recurrence5Scalar1Exceptional.coeff 304 =
      -(((((33113397774776162323384964863658748880335831316466196626355215 * 10 ^ 70 +
        2030245820197745037408267804193472334940003979815600664143044661570438) * 10 ^ 70 +
        7731948841090363990311577718554002089952746212325631462850963857478055) * 10 ^ 70 +
        3321408817935811388929074108168489821498497453768008659689291967650184) * 10 ^ 70 +
        8962513833021348295446192374472320426637694169306153050569189019880779) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 220 +
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
  rw [recurrence5Scalar1Exceptional_coeff_304_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_305 :
    recurrence5Scalar1Exceptional.coeff 305 =
      (((((4134647600920763657998087823270746013026158781131251033030323 * 10 ^ 70 +
        5211885157299677213954107800025786079790806686650601309867603524112830) * 10 ^ 70 +
        7372007289550291051137652388601305693454841164326168292665199685129666) * 10 ^ 70 +
        8168392890217541563617503016130114199551669461686245024123047423883623) * 10 ^ 70 +
        6973806495136521976788535896330107316019086699391966063193335561203039) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 221 +
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
  rw [recurrence5Scalar1Exceptional_coeff_305_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_306 :
    recurrence5Scalar1Exceptional.coeff 306 =
      (((((4671002347151380607114671083781042100036079228390287179990141 * 10 ^ 70 +
        9202065832472447395923740236353358338417086060525732807764012114499807) * 10 ^ 70 +
        5647398076141802624426274310845307394666113020924801559107709698694797) * 10 ^ 70 +
        1700301185950951919436992392596129747193412426880062590919775365100334) * 10 ^ 70 +
        7038830585227667618938497558154649178676469914840334026370951222694104) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 222 +
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
  rw [recurrence5Scalar1Exceptional_coeff_306_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_307 :
    recurrence5Scalar1Exceptional.coeff 307 =
      -(((((5813728130110272618222105728943630989872726793015110987663092 * 10 ^ 70 +
        1579621654521322291115104786674013133393136498858877513522180996194387) * 10 ^ 70 +
        8374398058926257655142400581557089721897387385489663160174410629384484) * 10 ^ 70 +
        2262797158667108006742941193467096653464609957753476728565443710694580) * 10 ^ 70 +
        6615725550427358301724608944295625508160650951551570917606866351687580) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 223 +
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
  rw [recurrence5Scalar1Exceptional_coeff_307_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_308 :
    recurrence5Scalar1Exceptional.coeff 308 =
      (((((4614304016100351155646169826445587172779229360677608044563906 * 10 ^ 70 +
        7316503006402655925793535342247106727468778623022994576608850837193821) * 10 ^ 70 +
        3211495373044170213436699483543432238780573455691939124735689448654862) * 10 ^ 70 +
        2097324796465829756999802138319455968572947913112266444685021617293094) * 10 ^ 70 +
        8294217612681322853237723162259892220281511769090284511042589525345852) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 224 +
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
  rw [recurrence5Scalar1Exceptional_coeff_308_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_309 :
    recurrence5Scalar1Exceptional.coeff 309 =
      -(((((3100683764175250952654110830580852981718419003445726520567389 * 10 ^ 70 +
        1014756951098591845617728313687176945683480425943347274251327928988998) * 10 ^ 70 +
        7135368946934172743139455704299352145547958457592108186397223051094321) * 10 ^ 70 +
        7066906143528747670294237786786453951119475519712148173655915319975186) * 10 ^ 70 +
        5520875679646292069861754336020785706918394841508575328504944827636465) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 225 +
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
  rw [recurrence5Scalar1Exceptional_coeff_309_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_310 :
    recurrence5Scalar1Exceptional.coeff 310 =
      (((((1896002549101735379835126613184426389938564871269551131163401 * 10 ^ 70 +
        6452937209023383590679481440801245467549180558483521831929592162971259) * 10 ^ 70 +
        1581944443225961064415511243271762803646085179075431947822698204640702) * 10 ^ 70 +
        9168016695323793865925000078635943015393097198940055881895110064013839) * 10 ^ 70 +
        6127711425110286108451148433747655515804115868047437686555287307775544) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 226 +
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
  rw [recurrence5Scalar1Exceptional_coeff_310_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_311 :
    recurrence5Scalar1Exceptional.coeff 311 =
      -(((((1086253637747435428092287765832583154912074506207486458159428 * 10 ^ 70 +
        8738754363248345660637910009216002035256572950610888500502854748757612) * 10 ^ 70 +
        7980916617328176377624000583664959409910163037161950468565309801212946) * 10 ^ 70 +
        1267120070751279701720559188110384733754387436586893065202713912727225) * 10 ^ 70 +
        4444473879957238848652286800638643357497436406012703473740348454982578) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 227 +
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
  rw [recurrence5Scalar1Exceptional_coeff_311_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_312 :
    recurrence5Scalar1Exceptional.coeff 312 =
      (((((591592078862754005774636869730402648189737602241727542022603 * 10 ^ 70 +
        2480684555672352392757487070987289789962571414503070424242799762416144) * 10 ^ 70 +
        8247460172782960513721843330588404728870155264127353308199750216027840) * 10 ^ 70 +
        5548687099684080796710968704563661244457038844568901733110826464437888) * 10 ^ 70 +
        8007290087827811187951509822475001517596153976171294970964572239128334) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 228 +
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
  rw [recurrence5Scalar1Exceptional_coeff_312_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_313 :
    recurrence5Scalar1Exceptional.coeff 313 =
      -(((((308734310422887587166239735704371038369313990622565140269504 * 10 ^ 70 +
        1120427714595969136705262202608106172420820933888822620287716438458754) * 10 ^ 70 +
        0231946716888885635136042418756191554988570985169952019674878082752406) * 10 ^ 70 +
        7562482797679991392922325709541253989876399852752305773646919831352342) * 10 ^ 70 +
        7325797459352441828825602491340694325600786863419390827448566526958970) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 229 +
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
  rw [recurrence5Scalar1Exceptional_coeff_313_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_314 :
    recurrence5Scalar1Exceptional.coeff 314 =
      (((((155109588914338751015361291217210627261121725835541085227408 * 10 ^ 70 +
        5969450583176196471892732959280059836462503435802714595250364046388881) * 10 ^ 70 +
        5124922530344770396606501288015294803676409746426052149964343127230583) * 10 ^ 70 +
        6586601272797775075821796152680510645248782348030372666026918859103777) * 10 ^ 70 +
        8512299441899321498810653141761551369269903375866119554722458665459702) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 230 +
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
  rw [recurrence5Scalar1Exceptional_coeff_314_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_315 :
    recurrence5Scalar1Exceptional.coeff 315 =
      -(((((75224456430485938957412291209310093188778988032263248083291 * 10 ^ 70 +
        7022991064830233405701581542818718181277742497084720659904193671546060) * 10 ^ 70 +
        6834608422447775168812335256178251489304811605220581039108711424162529) * 10 ^ 70 +
        3483309636688810351144890434525649029761296026832940424649850867781802) * 10 ^ 70 +
        3162182423418177375177557748160351368916134373083829546702481611172379) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 231 +
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
  rw [recurrence5Scalar1Exceptional_coeff_315_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_316 :
    recurrence5Scalar1Exceptional.coeff 316 =
      (((((35267701362564890166330323073760119169227118611558610769749 * 10 ^ 70 +
        3822792400449621848013063148671723138198260511291523228561175765351802) * 10 ^ 70 +
        4402486656264557369939472708996161391824092967335426722915439918123554) * 10 ^ 70 +
        0207406942721322696663991677851393037800185046749215148848437972079876) * 10 ^ 70 +
        8368188127475707522119804599722728104325405668808537787228498860876845) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 232 +
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
  rw [recurrence5Scalar1Exceptional_coeff_316_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_317 :
    recurrence5Scalar1Exceptional.coeff 317 =
      -(((((15993131249662743488641521959438521920580288705661011301158 * 10 ^ 70 +
        1716244486000171418084351733081113523429650806044909118625487631306952) * 10 ^ 70 +
        6570042249275407145980334006895948228998828725253970240975915104416637) * 10 ^ 70 +
        4571636536734256621103770925084091966336402634964243266205401533079964) * 10 ^ 70 +
        8106702835842227386085488216605836784271078350660931760052914484886250) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 233 +
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
  rw [recurrence5Scalar1Exceptional_coeff_317_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_318 :
    recurrence5Scalar1Exceptional.coeff 318 =
      (((((7013790966318288712463876735681971304931098541926183623548 * 10 ^ 70 +
        7677049879396178030856348132601614415463897077244417978499527426695060) * 10 ^ 70 +
        1158857347672944339843171032548403379777388292789994441966571716596914) * 10 ^ 70 +
        7161186112997905583954177680460161705492863179562399194290871015798888) * 10 ^ 70 +
        9550486145593604471419583035407546504867000415212675153205939588135677) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 234 +
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
  rw [recurrence5Scalar1Exceptional_coeff_318_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_319 :
    recurrence5Scalar1Exceptional.coeff 319 =
      -(((((2972123167155310182917980212662442403192674113224712824011 * 10 ^ 70 +
        6681925540004757555865206726908434457063462497021941476049483949395772) * 10 ^ 70 +
        8318939879639737641183119818110285429600816318060785310815392829724798) * 10 ^ 70 +
        7692019987367384320233774642862947369514521367422291375698430088302941) * 10 ^ 70 +
        2413927870265725000603307628995416258613677327970183381029602545294429) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 235 +
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
  rw [recurrence5Scalar1Exceptional_coeff_319_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_320 :
    recurrence5Scalar1Exceptional.coeff 320 =
      (((((1215047027753551584257597064479728000235608424355844315366 * 10 ^ 70 +
        1848215654257238522991243520960266835605604514522919251243644053773134) * 10 ^ 70 +
        3780906420273782787732917189200877611574559217785839304062841587162126) * 10 ^ 70 +
        8743186807356808355609731788612874723195023568037873675929883788630502) * 10 ^ 70 +
        7787938588465998377119817424191618405263636232704999682040932641763580) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 236 +
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
  rw [recurrence5Scalar1Exceptional_coeff_320_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_321 :
    recurrence5Scalar1Exceptional.coeff 321 =
      -(((((478039282776086856618740498993125595380931511756233849138 * 10 ^ 70 +
        5637059842954079145833172069281328476623728694141618127773784601443400) * 10 ^ 70 +
        5809548147360626780136648205991348859417024707118102631354046179937864) * 10 ^ 70 +
        8185342466405765308279844764886535904349564886756860991712108286805056) * 10 ^ 70 +
        0859416933651363700206483970492122788506535994695808029687593003221841) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 237 +
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
  rw [recurrence5Scalar1Exceptional_coeff_321_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_322 :
    recurrence5Scalar1Exceptional.coeff 322 =
      (((((180333602683926411622602327681303131179307260611981103476 * 10 ^ 70 +
        4165927478334100717001854570395666135674894688327838073618988153541134) * 10 ^ 70 +
        4952572159526558636913667027877043992921782024828113985327506815962413) * 10 ^ 70 +
        5017561889848859904376708259530697182341855669330329500642730044841206) * 10 ^ 70 +
        3813411691817927782819269562480796871483262593761036854425122025317335) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 238 +
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
  rw [recurrence5Scalar1Exceptional_coeff_322_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_323 :
    recurrence5Scalar1Exceptional.coeff 323 =
      -(((((64865099787098036885468831982206842004882760471774892329 * 10 ^ 70 +
        2344067815364828908897580512753268128341299978092932657733526383330833) * 10 ^ 70 +
        3313978899076186803850838635386369412274424379764882917298228818842460) * 10 ^ 70 +
        9215776413256651281728957815474588840145243601226904156697368115647089) * 10 ^ 70 +
        8482361915133668913866176953750623199244577529181944745301861819811441) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 239 +
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
  rw [recurrence5Scalar1Exceptional_coeff_323_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_324 :
    recurrence5Scalar1Exceptional.coeff 324 =
      (((((22052171747652819730084084327156419324728406674009530090 * 10 ^ 70 +
        0855347826189440143303222277969553218555243959049741823132764780245702) * 10 ^ 70 +
        7370667966585193078133254468470435804009735752394205584541233679236910) * 10 ^ 70 +
        3959164971770834002782618082678762001710082918635994163980169343374383) * 10 ^ 70 +
        8188893097391620836580527758357817571200437152373348226351392579413047) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 240 +
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
  rw [recurrence5Scalar1Exceptional_coeff_324_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_325 :
    recurrence5Scalar1Exceptional.coeff 325 =
      -(((((6981011669672070519985349627760637352612396227073839934 * 10 ^ 70 +
        5027765386547813225744794496560707950194217922244858582751565125944649) * 10 ^ 70 +
        8845980339990468045384821544399002579451499977613770536618675050220377) * 10 ^ 70 +
        5624658571123163307256479718753962067520842758335017743378930544127419) * 10 ^ 70 +
        7753547572611481984716537196835687717188725480354233610496663427349524) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 241 +
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
  rw [recurrence5Scalar1Exceptional_coeff_325_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_326 :
    recurrence5Scalar1Exceptional.coeff 326 =
      (((((1999858745158829028214438147947654915518198019015823521 * 10 ^ 70 +
        8307057339007534552660487504389589948808404680234984301752899923691977) * 10 ^ 70 +
        2671627439663202879187637599928182654042814804714676442591830138972059) * 10 ^ 70 +
        0968248614791247058183394779947883289182477064285294528339723916798317) * 10 ^ 70 +
        8566732533944146170855815274574245540672066665148344313710189723404370) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 242 +
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
  rw [recurrence5Scalar1Exceptional_coeff_326_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_327 :
    recurrence5Scalar1Exceptional.coeff 327 =
      -(((((484720331802151986880896302363276792789003023737551908 * 10 ^ 70 +
        5865095297748752657756007736750370234042020939356254694061379614582314) * 10 ^ 70 +
        8104045950323732958557253867601225995495482140669063743823412741390613) * 10 ^ 70 +
        9206281510714607533395738512054676018721273528456948854550869149185957) * 10 ^ 70 +
        0295889342601187443861164830347895592559198704165222419871963452251559) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 243 +
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
  rw [recurrence5Scalar1Exceptional_coeff_327_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_328 :
    recurrence5Scalar1Exceptional.coeff 328 =
      (((((77861536712291491708012776883206647641357475860885129 * 10 ^ 70 +
        2610591834274528081771344846341414937030376070219550412612166349370301) * 10 ^ 70 +
        5854990467950952421482663394239840253492705391096723559179693004860231) * 10 ^ 70 +
        3657551972455340497836380386495205882003780280351882765260590260244593) * 10 ^ 70 +
        9843626522737024016973070227505302914106098081710023993382292848590447) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 244 +
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
  rw [recurrence5Scalar1Exceptional_coeff_328_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_329 :
    recurrence5Scalar1Exceptional.coeff 329 =
      (((((8126401939503980184450867628234518997285216109678171 * 10 ^ 70 +
        7647392716210606420681078988351276270453133800289514578482796253131088) * 10 ^ 70 +
        4266831296589251166326088693276361197858267053088178422998294764974771) * 10 ^ 70 +
        7763646083356178121945953354599163559553189548498041285307639520610455) * 10 ^ 70 +
        1651303444807034270784779271336075132841634483608662288007128364352557) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 245 +
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
  rw [recurrence5Scalar1Exceptional_coeff_329_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_330 :
    recurrence5Scalar1Exceptional.coeff 330 =
      -(((((15246245627741143772919045949981919875916086434618208 * 10 ^ 70 +
        8835145513846801574757700830299502947763394805592428366667424293761300) * 10 ^ 70 +
        6632749950723100508657894475440806410057627848997073317894914982082012) * 10 ^ 70 +
        2895286581779338666999919499609777453085357039257918615267227989463828) * 10 ^ 70 +
        8920206205865641610199732401547086912070007976198376064670287596597163) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 246 +
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
  rw [recurrence5Scalar1Exceptional_coeff_330_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_331 :
    recurrence5Scalar1Exceptional.coeff 331 =
      (((((9254908671688260651927566640942805577190487360533495 * 10 ^ 70 +
        3276153868752118794615668001263701327595196750511866630458334517647914) * 10 ^ 70 +
        5697926328906464205326135870203281712757284402560007858315228274994625) * 10 ^ 70 +
        1699988547309295459071875461866164105662626299403457987770891240789097) * 10 ^ 70 +
        6145759776017619669544442234239339141293733529963060871653996682945785) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 247 +
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
  rw [recurrence5Scalar1Exceptional_coeff_331_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_332 :
    recurrence5Scalar1Exceptional.coeff 332 =
      -(((((4319821131833427383040214637498717849476732129400851 * 10 ^ 70 +
        4848212410898169628985496604213460449187438998516425427537818910269755) * 10 ^ 70 +
        8076832301906452549701834300265481725849663146342304017639946919728213) * 10 ^ 70 +
        8796827427237555952711892048572365813861143044823285927930365223333864) * 10 ^ 70 +
        6980985354103466425723797752063306171287989288070192642716925408488194) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 248 +
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
  rw [recurrence5Scalar1Exceptional_coeff_332_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_333 :
    recurrence5Scalar1Exceptional.coeff 333 =
      (((((1747622127038377971062145729835989237027452181159534 * 10 ^ 70 +
        3296083489987224451314962463871752037964913066688202853144640179415596) * 10 ^ 70 +
        1968911602776110751114647211754655854592776129221501207621350215328084) * 10 ^ 70 +
        0287544163425640912717117930368691771557350574785662358533292025268778) * 10 ^ 70 +
        3924126803526320677564889074231724570995063375023465971410991278836101) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 249 +
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
  rw [recurrence5Scalar1Exceptional_coeff_333_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_334 :
    recurrence5Scalar1Exceptional.coeff 334 =
      -(((((635339146479526744844525977548147957893270839437356 * 10 ^ 70 +
        8723987386329382815258709936816226501015950984857245032122531359028594) * 10 ^ 70 +
        6879044360023657780082680199773604625843587210992066139241757215942555) * 10 ^ 70 +
        6613250799411628561955577212223237206877247989302030354843464665967880) * 10 ^ 70 +
        3771722408302227825574465883559368806489368478299092062614340662358812) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 250 +
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
  rw [recurrence5Scalar1Exceptional_coeff_334_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_335 :
    recurrence5Scalar1Exceptional.coeff 335 =
      (((((209194254483602807658920542913687090879569992194341 * 10 ^ 70 +
        9108957905292913895469047552757696021912230599305592281259996187141056) * 10 ^ 70 +
        2162779394349198559939729806308351975693511655217984107303577010720691) * 10 ^ 70 +
        4828001542744057983429234562266906663816057272315892698463598359293136) * 10 ^ 70 +
        4193549275290365002693357750025967380594916099274339267123312354962983) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 251 +
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
  rw [recurrence5Scalar1Exceptional_coeff_335_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_336 :
    recurrence5Scalar1Exceptional.coeff 336 =
      -(((((61584159681038880895881276245662144797017117176693 * 10 ^ 70 +
        5178792525775210333431253996829469749529590430039930917782830266119011) * 10 ^ 70 +
        4638097905452300714238389262424997136411306032386741402145127429960691) * 10 ^ 70 +
        5613974374662441500125474948065331907124178986790219710863645761922345) * 10 ^ 70 +
        5445367242037811729184588465974465336798047249434946192391928925334805) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 252 +
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
  rw [recurrence5Scalar1Exceptional_coeff_336_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_337 :
    recurrence5Scalar1Exceptional.coeff 337 =
      (((((15429579901558915792964763425826157400843550148296 * 10 ^ 70 +
        8440760055702001509876671355348797146950151448394935889974304885471537) * 10 ^ 70 +
        1319541170483211763497852548286899629984325128972728762828133989469250) * 10 ^ 70 +
        8909507784821729559142504523895820827572662328990914363375762544884262) * 10 ^ 70 +
        0533880515808910107612647127168340047337642397201838593518440739757148) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 253 +
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
  rw [recurrence5Scalar1Exceptional_coeff_337_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_338 :
    recurrence5Scalar1Exceptional.coeff 338 =
      -(((((2734952455314359614882960253713500537153820758548 * 10 ^ 70 +
        8017085747324932001942561608264515471434045979438481262375580491951788) * 10 ^ 70 +
        3351016739646060159876422657273205357529204856790556606293268608179840) * 10 ^ 70 +
        5936877931403023670423429507348164724652378639288367325245666560452196) * 10 ^ 70 +
        0206622658544787836539521359931401777990613947951811554585943848772698) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 254 +
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
  rw [recurrence5Scalar1Exceptional_coeff_338_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_339 :
    recurrence5Scalar1Exceptional.coeff 339 =
      -(((((81040370980485816639449006824007682511888742129 * 10 ^ 70 +
        7731761691183368318028346891005859999479621939810812862942480851404044) * 10 ^ 70 +
        9279810921752873544246185583691496613430750411894578998707373533163721) * 10 ^ 70 +
        9469218147666766576471325414557801709406084865970168929214284633710343) * 10 ^ 70 +
        8525411881438792921576898199252388265006774511832766977764998106014362) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 255 +
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
  rw [recurrence5Scalar1Exceptional_coeff_339_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_340 :
    recurrence5Scalar1Exceptional.coeff 340 =
      (((((402208908599656776209346551471535618426780403516 * 10 ^ 70 +
        4199961728558388142449922457787110681520853501290915642002292695468655) * 10 ^ 70 +
        0231198593669349289425638144452860793169218154053155327863475396997753) * 10 ^ 70 +
        5630107843837263268516293600504168715392537983267567229257419494183747) * 10 ^ 70 +
        8855545960504404500639531312441036181746144370525383548539226579751483) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 256 +
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
  rw [recurrence5Scalar1Exceptional_coeff_340_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_341 :
    recurrence5Scalar1Exceptional.coeff 341 =
      -(((((267078415310845634386953310686379153337290240019 * 10 ^ 70 +
        7709083393891788467575458427142257399634897133668602779539620417458167) * 10 ^ 70 +
        4786596119627125079420982816783361508068467089703605870584680246613824) * 10 ^ 70 +
        4538082373810817947754275777691261817451942576474293422516951254438812) * 10 ^ 70 +
        6458440492166347077933961436088670524389267793251847406719454188009365) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 257 +
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
  rw [recurrence5Scalar1Exceptional_coeff_341_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_342 :
    recurrence5Scalar1Exceptional.coeff 342 =
      (((((133723449586943034896151794740785115726301267971 * 10 ^ 70 +
        1667083386308073153582294648791639583752019235818318544143219083425158) * 10 ^ 70 +
        7006019118262088772749428638665364686464945374786046389741343703533518) * 10 ^ 70 +
        5339476298611267763379372299137892121106767178999834593417367571483704) * 10 ^ 70 +
        6186842756231655662558854073053159637598857676801415716209031872848084) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 258 +
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
  rw [recurrence5Scalar1Exceptional_coeff_342_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_343 :
    recurrence5Scalar1Exceptional.coeff 343 =
      -(((((58839627817863544061256268333089099302491065759 * 10 ^ 70 +
        0749961105298030121703652525509599976361151008206109815935006886876145) * 10 ^ 70 +
        7519608544907787504765732112800854597188421393322421935217719801262960) * 10 ^ 70 +
        4538832213950401117162286024149642774350948748394770134814389320479573) * 10 ^ 70 +
        6446675750329104331502706389596598746649681867458471739723523883047713) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 259 +
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
  rw [recurrence5Scalar1Exceptional_coeff_343_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_344 :
    recurrence5Scalar1Exceptional.coeff 344 =
      (((((23902528491922152207686096022476478414085241162 * 10 ^ 70 +
        2401381668388931850584234003729547855386011767334759654063696803358584) * 10 ^ 70 +
        7690883300409647869834031260036189980626838315647016050898286963548101) * 10 ^ 70 +
        7055217301492979229654468034212956994014069881872144106162065146794960) * 10 ^ 70 +
        1505035180874924208931075550105729660221781673345030197479493069723496) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 260 +
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
  rw [recurrence5Scalar1Exceptional_coeff_344_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_345 :
    recurrence5Scalar1Exceptional.coeff 345 =
      -(((((9153553349687627416391302121318036985317956410 * 10 ^ 70 +
        9500514532383380878808259053686532860525895826414339445436338474372300) * 10 ^ 70 +
        4242803297222991990868388263756268872257061228508524795596362576638048) * 10 ^ 70 +
        8348956387657799879343714778264853626481437195434896186575395182809083) * 10 ^ 70 +
        5113949829505211382266302513593953058986996059303887167367497311307649) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 261 +
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
  rw [recurrence5Scalar1Exceptional_coeff_345_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_346 :
    recurrence5Scalar1Exceptional.coeff 346 =
      (((((3334400357466118024108734900302917687557552068 * 10 ^ 70 +
        5767661180712230673164892299297370807410419945257195440934048490202073) * 10 ^ 70 +
        6826978935726655523772531165889704540101313480163138255582896871101936) * 10 ^ 70 +
        2864461878407775405441009202852258479722634764945473881048375449277576) * 10 ^ 70 +
        0837869031911742602114148512749332464003045153629580136140027025846660) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 262 +
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
  rw [recurrence5Scalar1Exceptional_coeff_346_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_347 :
    recurrence5Scalar1Exceptional.coeff 347 =
      -(((((1158194710414622711298915113440740036274471789 * 10 ^ 70 +
        3509078228424177566003339464022694074194779181189024017947777892321998) * 10 ^ 70 +
        5817961999318667920099117573301903821394556200258621437290707493800896) * 10 ^ 70 +
        7905523156218485765538534731855631946533410478643613817025735938008151) * 10 ^ 70 +
        0465727274149115158448472280828254272299979876477661429811633494621795) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 263 +
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
  rw [recurrence5Scalar1Exceptional_coeff_347_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_348 :
    recurrence5Scalar1Exceptional.coeff 348 =
      (((((382673093658485417459159973596297932506329533 * 10 ^ 70 +
        7903283754059241976694202722500910665112607037140577304278758083911724) * 10 ^ 70 +
        4356995049101435676922336804990880352286697544940552877030562757941729) * 10 ^ 70 +
        5242377055188438959706294880553689283320735320643139712322506507510854) * 10 ^ 70 +
        0161081615636516846920541916496897395256603472050134731452380049299414) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 264 +
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
  rw [recurrence5Scalar1Exceptional_coeff_348_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_349 :
    recurrence5Scalar1Exceptional.coeff 349 =
      -(((((119373747711411199822890203618362959449244512 * 10 ^ 70 +
        3199614331624638041905458110430565299686935211409030530284302445565912) * 10 ^ 70 +
        7187331966248077293236105539919032517743072509383751281090833527260509) * 10 ^ 70 +
        2213215775249262433417892244615975582738379784413545308935593478377003) * 10 ^ 70 +
        3262225453198645306268866976284460076583168827840552479132015300259193) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 265 +
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
  rw [recurrence5Scalar1Exceptional_coeff_349_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_350 :
    recurrence5Scalar1Exceptional.coeff 350 =
      (((((34631825903211563427030094396092625626883436 * 10 ^ 70 +
        3637163421005611407584386197964338247307441078803835845115272742296868) * 10 ^ 70 +
        6435424812227948311523353177894022837735373861158786489643684354883156) * 10 ^ 70 +
        8091365039974052889843313731313511158408112144633632340384924573625807) * 10 ^ 70 +
        6212800371923704749428507700787449477636205783352632421258116131302639) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 266 +
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
  rw [recurrence5Scalar1Exceptional_coeff_350_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_351 :
    recurrence5Scalar1Exceptional.coeff 351 =
      -(((((9060073319498182279483337602284312981224155 * 10 ^ 70 +
        3379300031660528240808969335384997487244437437887340467255801539665185) * 10 ^ 70 +
        1883261640104399655812175123648716329859505528051762640598879332248068) * 10 ^ 70 +
        3105559649516206910159790436576284988657210215688674091694362391810899) * 10 ^ 70 +
        3131014360964627736100802757432352929306512751475336343215006569663515) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 267 +
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
  rw [recurrence5Scalar1Exceptional_coeff_351_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_352 :
    recurrence5Scalar1Exceptional.coeff 352 =
      (((((1980805415110950226785422581237959111331404 * 10 ^ 70 +
        6077208096436068162819672188159011079605083749592721312924584591586016) * 10 ^ 70 +
        0136635402356955216713299516926067081844486762571373079317422777178452) * 10 ^ 70 +
        0332941528207659112108562441721996734402502956215816799871171674461229) * 10 ^ 70 +
        8642966982160865965161846896532237436747907728990589949134043225975465) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 268 +
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
  rw [recurrence5Scalar1Exceptional_coeff_352_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_353 :
    recurrence5Scalar1Exceptional.coeff 353 =
      -(((((267079821905026861913180138214117410530287 * 10 ^ 70 +
        5827570032593957263189839498320923859513547138988863686770425336561754) * 10 ^ 70 +
        4545417911743910956211709153424021451246576800529251510315009364458497) * 10 ^ 70 +
        2198622315983760114958133463995191209840449788823601811307087223639683) * 10 ^ 70 +
        5065595152818344446875233371717446419002494245239153660565765732659075) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 269 +
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
  rw [recurrence5Scalar1Exceptional_coeff_353_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_354 :
    recurrence5Scalar1Exceptional.coeff 354 =
      -(((((47261386385872206784789243332408512775726 * 10 ^ 70 +
        1864979315576653861209538746856005343652902846757924139213590974700885) * 10 ^ 70 +
        4617285413781203757402496551314482735394891759229801208306565038523058) * 10 ^ 70 +
        0733953855141036493579126635797454520690722829223901947804133439735002) * 10 ^ 70 +
        4816407298827207925458014613797478616030477341731584400498614950958267) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 270 +
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
  rw [recurrence5Scalar1Exceptional_coeff_354_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_355 :
    recurrence5Scalar1Exceptional.coeff 355 =
      (((((58990211533446386351951608782454589379343 * 10 ^ 70 +
        1336605342937779435436828718971918703278144154647917440141763161121056) * 10 ^ 70 +
        5091485735091181158220063415763223759966463329144166836215258326166521) * 10 ^ 70 +
        7226855921126700900460309438764342699943266624889307355888172181939574) * 10 ^ 70 +
        8667569202765513416766200227818733895095211477718520407013536810627947) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 271 +
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
  rw [recurrence5Scalar1Exceptional_coeff_355_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_356 :
    recurrence5Scalar1Exceptional.coeff 356 =
      -(((((32031465184738691773383630543096320957036 * 10 ^ 70 +
        9003370879004421278673987258412615222799225317253253923816855661100680) * 10 ^ 70 +
        1723939659020909403905686029289426188207140210641086437176410431609265) * 10 ^ 70 +
        9859303566555886483261156019004737358402035062928851169197044543137963) * 10 ^ 70 +
        9458781302589531653694376921577940491158784067639286086839404067659977) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 272 +
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
  rw [recurrence5Scalar1Exceptional_coeff_356_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_357 :
    recurrence5Scalar1Exceptional.coeff 357 =
      (((((13738430732557445524402460612600878878175 * 10 ^ 70 +
        3859817466826495102336465023362331377701800623219817222617135512072499) * 10 ^ 70 +
        7214536189972890627029895659658517831908125588066505656192917904463140) * 10 ^ 70 +
        0718008799824100138555753713518867925882572803911819238733915676165961) * 10 ^ 70 +
        1928361147341520149150869176948753002888712462638078249254874815788444) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 273 +
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
  rw [recurrence5Scalar1Exceptional_coeff_357_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_358 :
    recurrence5Scalar1Exceptional.coeff 358 =
      -(((((5156345427773385883265017335810439536746 * 10 ^ 70 +
        8652027466152951225390660562433768607423437921394780503940774534790767) * 10 ^ 70 +
        0701891186671169555585688653061012278229900498263135241650076130008448) * 10 ^ 70 +
        7909006583864366657026595870050688013559773752123186266441039343087548) * 10 ^ 70 +
        0753634729278113521235580606457861387664395209928985048894529338895339) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 274 +
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
  rw [recurrence5Scalar1Exceptional_coeff_358_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_359 :
    recurrence5Scalar1Exceptional.coeff 359 =
      (((((1749711673750835383947621983870512545048 * 10 ^ 70 +
        0437166052981821607116271548929083825831919623984161938241015644286022) * 10 ^ 70 +
        9469528524586038208465078211491511545177364746952252548437638959624703) * 10 ^ 70 +
        2957585194575848144229372610151566082047802656856137387097990651995777) * 10 ^ 70 +
        7221392379918481387025622535080577387491218885645145815226817058217022) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 275 +
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
  rw [recurrence5Scalar1Exceptional_coeff_359_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_360 :
    recurrence5Scalar1Exceptional.coeff 360 =
      -(((((541163250491718480901443052095624296990 * 10 ^ 70 +
        0498163821002152855502187280663492472550929379594495678473931394721388) * 10 ^ 70 +
        5467369083178315787558655682050358172107589689813809516944928928360240) * 10 ^ 70 +
        5841643311505637930489644836621783983729439216982125201560182115151775) * 10 ^ 70 +
        5377553771487067974983906302442543569672985746446540381845985749808827) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 276 +
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
  rw [recurrence5Scalar1Exceptional_coeff_360_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_361 :
    recurrence5Scalar1Exceptional.coeff 361 =
      (((((151130339649268977957121329015420917151 * 10 ^ 70 +
        1245433414378203073616486046753254513588531819050012076404856395760485) * 10 ^ 70 +
        3773863139007249485825094828394471945567352138621081771918211733361872) * 10 ^ 70 +
        0058736149291785062930535936447732577688416195577924357730899831990765) * 10 ^ 70 +
        9101045280408994181716794713036233944588889443928660146114953704830794) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 277 +
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
  rw [recurrence5Scalar1Exceptional_coeff_361_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_362 :
    recurrence5Scalar1Exceptional.coeff 362 =
      -(((((36707239259328763023605099603840680132 * 10 ^ 70 +
        1888460396002603313116876070513469151371004624326379705866940433037483) * 10 ^ 70 +
        8034380775870744233241290408199427839807890527477638378704864036046058) * 10 ^ 70 +
        1507892569513594425568073667779004652765158332677933094715454218777644) * 10 ^ 70 +
        3992679187290564154597576533183298022141780689642617935645373623027156) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 278 +
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
  rw [recurrence5Scalar1Exceptional_coeff_362_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_363 :
    recurrence5Scalar1Exceptional.coeff 363 =
      (((((6825196189979622334377593098527800209 * 10 ^ 70 +
        4896054940028876358320530476486956122006328182559294772518145984965249) * 10 ^ 70 +
        1636480896595808921238946524694235743242266133711861086956536501527129) * 10 ^ 70 +
        7988513881951892224500755503245810202443276658883212309282755332896452) * 10 ^ 70 +
        6369062363935424446244843168612036605218193867972179999203185433746097) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 279 +
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
  rw [recurrence5Scalar1Exceptional_coeff_363_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_364 :
    recurrence5Scalar1Exceptional.coeff 364 =
      -(((((335051390301929325266190219898849797 * 10 ^ 70 +
        0579635457394470459142619503814701793175143107540083887137670787450485) * 10 ^ 70 +
        0297528816682696706320552618802005861629571590922235002997781311971284) * 10 ^ 70 +
        6496909259551424549719466739771756761208134690560390233441497896562349) * 10 ^ 70 +
        8501424793373942213308581775506468948193005773615376165162822384396213) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 280 +
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
  rw [recurrence5Scalar1Exceptional_coeff_364_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_365 :
    recurrence5Scalar1Exceptional.coeff 365 =
      -(((((537580659299944473373727615342644919 * 10 ^ 70 +
        8836397963561981081291167315708230092196455439983374725417450059777341) * 10 ^ 70 +
        7566946105322926248094615959884648671836328172966406622717945591973085) * 10 ^ 70 +
        0174478185071296706143344096130720758143574303872375281080542371919564) * 10 ^ 70 +
        1089857623412900736801931091864464385724054568562637812230403630145609) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 281 +
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
  rw [recurrence5Scalar1Exceptional_coeff_365_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_366 :
    recurrence5Scalar1Exceptional.coeff 366 =
      (((((385132035321086405013471593156636357 * 10 ^ 70 +
        3926881288780403815188696611594908489721669575992350250803940628475098) * 10 ^ 70 +
        4083343215925094184405288366887787699209885540283613059273914490612993) * 10 ^ 70 +
        3326839667055013251070790885186123154440385105444008241632348990438983) * 10 ^ 70 +
        6966422850652579502261695064284022734895961602507637733964572382846910) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 282 +
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
  rw [recurrence5Scalar1Exceptional_coeff_366_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_367 :
    recurrence5Scalar1Exceptional.coeff 367 =
      -(((((190656661908334444520109906449471415 * 10 ^ 70 +
        8643770018342837543577497445696953832837824290195961109991708329495608) * 10 ^ 70 +
        3127826255608607298946954701973340433167974572773052510001373657902663) * 10 ^ 70 +
        1336078088732733284582837563069326774387150383979032694202963161303523) * 10 ^ 70 +
        7067104197691440522982311166212805944086087347012323064488538657417056) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 283 +
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
  rw [recurrence5Scalar1Exceptional_coeff_367_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_368 :
    recurrence5Scalar1Exceptional.coeff 368 =
      (((((81446077707704404923859971757567868 * 10 ^ 70 +
        6290808018099563714050349034431407688514736132452956580817848823369224) * 10 ^ 70 +
        9184527970155464861965845019485505720419484731859914829228011290710557) * 10 ^ 70 +
        1954906211961058604666692007235644681054488544698306872415761618234113) * 10 ^ 70 +
        5038591507658433483446204181547635884052059415290816394671701460460607) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 284 +
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
  rw [recurrence5Scalar1Exceptional_coeff_368_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_369 :
    recurrence5Scalar1Exceptional.coeff 369 =
      -(((((31950634731797665187948212561793699 * 10 ^ 70 +
        8789032558951927899188710443177660477597844197660274160101282854375674) * 10 ^ 70 +
        0527309907261861761084388968543667224104591652289535725497008734838407) * 10 ^ 70 +
        0277976010826250930243208474564831858097709145069618203153750825491799) * 10 ^ 70 +
        4595676268680372984980397577579463019490824889305070683460271718543468) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 285 +
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
  rw [recurrence5Scalar1Exceptional_coeff_369_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_370 :
    recurrence5Scalar1Exceptional.coeff 370 =
      (((((11802351565883735350439060545799904 * 10 ^ 70 +
        4072508794551959653527261955591603217130545322056826549122372609009685) * 10 ^ 70 +
        8624532112052407312238138347102498434332591768840383597575406033675105) * 10 ^ 70 +
        7162039955423633427915552063865302125385568545025100187127098554459707) * 10 ^ 70 +
        5887403245175250888619853839394337252871385215932935528770598148100553) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 286 +
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
  rw [recurrence5Scalar1Exceptional_coeff_370_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_371 :
    recurrence5Scalar1Exceptional.coeff 371 =
      -(((((4151575692487954759621635054455146 * 10 ^ 70 +
        8123538375452406661585830968773567100729794909133451599103908990782836) * 10 ^ 70 +
        6061006220144135090276760541345863022595568282023184964943569678212611) * 10 ^ 70 +
        7250785300715521649601804351547649406467849503789994611841587001118272) * 10 ^ 70 +
        3100986671066200185033705018492747778686696555208849934299074798913662) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 287 +
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
  rw [recurrence5Scalar1Exceptional_coeff_371_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_372 :
    recurrence5Scalar1Exceptional.coeff 372 =
      (((((1396977176688767010229058270933971 * 10 ^ 70 +
        3898534638661191382717582269449854485382620746166511572105773310425618) * 10 ^ 70 +
        3616445112377973315310413233921043781844889409070420363914278873934221) * 10 ^ 70 +
        0714916670881558875137488451832149850187453754069304891399508786705469) * 10 ^ 70 +
        6675332264834107210765439637421117808960304899461119911392187453776825) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 288 +
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
  rw [recurrence5Scalar1Exceptional_coeff_372_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_373 :
    recurrence5Scalar1Exceptional.coeff 373 =
      -(((((449930429576492523855406377661078 * 10 ^ 70 +
        9086279470277145081138010384731707949547581201974783316311401565058105) * 10 ^ 70 +
        9444766442148752396658928920497081468003927795385358929489422769696091) * 10 ^ 70 +
        4903830008237716743740966598657466036724711253764137825582624631532209) * 10 ^ 70 +
        0012297041627205886632018402135091614376852412412099936051171353566937) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 289 +
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
  rw [recurrence5Scalar1Exceptional_coeff_373_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_374 :
    recurrence5Scalar1Exceptional.coeff 374 =
      (((((138356538244971380793203761675903 * 10 ^ 70 +
        2567135025328605012601989536090009122841369646219199378368039291790714) * 10 ^ 70 +
        0041021605373745024481856213176172335900815938663205780477854673609335) * 10 ^ 70 +
        5374429638304225483813682824717719623615826946994578546562276414927401) * 10 ^ 70 +
        5524079130367233250183145987619988117103747597872694589512097999581034) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 290 +
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
  rw [recurrence5Scalar1Exceptional_coeff_374_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_375 :
    recurrence5Scalar1Exceptional.coeff 375 =
      -(((((40390647692496897602028792000807 * 10 ^ 70 +
        1365273769037002300810960150068439107140349463836652236541637798534459) * 10 ^ 70 +
        4865494810803222852792205834690992411463750722334160466533820365053543) * 10 ^ 70 +
        7363812260577444529736389170885220408368718792369826731075282566183893) * 10 ^ 70 +
        3312748335051808481244012538112092240458919925516901077592117526202094) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 291 +
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
  rw [recurrence5Scalar1Exceptional_coeff_375_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_376 :
    recurrence5Scalar1Exceptional.coeff 376 =
      (((((11080681258211045594060379719641 * 10 ^ 70 +
        8430386298690790997323760873421495994950331875878726894326820094431111) * 10 ^ 70 +
        6806204629014384672902222285691673615601577713864945876415616334015834) * 10 ^ 70 +
        2378804412000522547069905577629983526936664123907249328373703013382123) * 10 ^ 70 +
        5331715206942105096665365368205315896462119236984470017753399767578347) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 292 +
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
  rw [recurrence5Scalar1Exceptional_coeff_376_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_377 :
    recurrence5Scalar1Exceptional.coeff 377 =
      -(((((2805048017336980407512006482125 * 10 ^ 70 +
        1529939714035272224715538428966451088007470380717930898506675228244312) * 10 ^ 70 +
        9383658844561448443182810364606645796490831803434077899246910434044133) * 10 ^ 70 +
        0857864541465381078282787842363649042879291257099361168617467167641808) * 10 ^ 70 +
        8770597141551202510004275950089561831809807010226440454806293042752111) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 293 +
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
  rw [recurrence5Scalar1Exceptional_coeff_377_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_378 :
    recurrence5Scalar1Exceptional.coeff 378 =
      (((((631811094125512386324115626766 * 10 ^ 70 +
        4704795579768330229819496611085518733846060293222469285798312582844999) * 10 ^ 70 +
        7887945126677299934031727596744433524680716473018167201678958192009070) * 10 ^ 70 +
        8673235584992385875554192407136583602453828712174518011762902871582817) * 10 ^ 70 +
        6558154213132174566452851719404353982982637825023253010277294521099336) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 294 +
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
  rw [recurrence5Scalar1Exceptional_coeff_378_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (379 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_379 :
    recurrence5Scalar1Exceptional.coeff 379 =
      -(((((115435175388248151907451605707 * 10 ^ 70 +
        5128236481507551169973154495033581130183913160532866431827403293577526) * 10 ^ 70 +
        0299743598892304428315460692847188585155545845893889812806702642411776) * 10 ^ 70 +
        6571940223318434590438368714813512618838953783626326765074108168202465) * 10 ^ 70 +
        3840503529101792003562746334725883633283789788925310481444532102908910) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 295 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (380 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_380 :
    recurrence5Scalar1Exceptional.coeff 380 =
      (((((11145060379671509390076018971 * 10 ^ 70 +
        8616090231280127423001051800686795421873048182056879424908250705105199) * 10 ^ 70 +
        2348418807020182488015426883055738268612013504610685780884544569142601) * 10 ^ 70 +
        3534607364209309460663186629821569329386910869885775808711311437221768) * 10 ^ 70 +
        3198663836583949461364904354460066226385467586632265947381239727139257) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 296 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 19 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (381 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_381 :
    recurrence5Scalar1Exceptional.coeff 381 =
      (((((3348346565696827143006259034 * 10 ^ 70 +
        5090455371168827787020641916174540767421330327184298824428567599279489) * 10 ^ 70 +
        8028345843841891718973977870437021191556736587976338239541777740387820) * 10 ^ 70 +
        2499714571759595654879098104989517916332267609683394843110852346728130) * 10 ^ 70 +
        7353553954342636819098959476979770314948466918740681799810912971453657) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 297 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 18 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (382 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_382 :
    recurrence5Scalar1Exceptional.coeff 382 =
      -(((((2693932424234780832732179796 * 10 ^ 70 +
        7939370384181989085740599666174518174687176511873715594867390238449170) * 10 ^ 70 +
        5613591143740190468099800902375411884740473474323579170096392345481543) * 10 ^ 70 +
        1107386843702531298426163501717945059701195247917293286976903881490692) * 10 ^ 70 +
        2532476871669128489390378079155905090430769563701637107283673680172257) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 298 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 17 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (383 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_383 :
    recurrence5Scalar1Exceptional.coeff 383 =
      (((((1169741903514739228169303032 * 10 ^ 70 +
        4599689310492587555709914481627144398394924081208238957340049827934653) * 10 ^ 70 +
        4918178949042169382598538356813816906518133874283115221498808695219102) * 10 ^ 70 +
        6312653828029490289555233434123914545080948996610428947186471965266142) * 10 ^ 70 +
        6842377183872408007101224732911221312334091227167109821289409289013396) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 299 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 16 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (384 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_384 :
    recurrence5Scalar1Exceptional.coeff 384 =
      -(((((407818674991069471072099327 * 10 ^ 70 +
        1707616238817509460113103632230947948255867346780382005128646999325795) * 10 ^ 70 +
        7178200176832715883436823019781487838943069612732169002119525900956203) * 10 ^ 70 +
        8624435156209798582142264696978638841849770302993300748809283420613219) * 10 ^ 70 +
        8863240518158489851059806051756928804111227288194957268347597665759804) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 300 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 15 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (385 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_385 :
    recurrence5Scalar1Exceptional.coeff 385 =
      (((((124029176712217823530993161 * 10 ^ 70 +
        3533897846538950921237813271891079400678998853792269886330834714133944) * 10 ^ 70 +
        7967271712819935147580035241737837592901155065811736736060001790650435) * 10 ^ 70 +
        9830264745169305388604149306634704312969034232020088405783282238554468) * 10 ^ 70 +
        3692351263947414041517931595639707054594848439420939724092069327356557) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 301 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 14 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (386 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_386 :
    recurrence5Scalar1Exceptional.coeff 386 =
      -(((((33818888281238083708044722 * 10 ^ 70 +
        5787319771452155005715279128753488239497588956432081602045280942640179) * 10 ^ 70 +
        8065750652931011865484047066797981193317295467419918480471458936866646) * 10 ^ 70 +
        0473985156845036009552890560151781681904138535989897121975799567673662) * 10 ^ 70 +
        8332570772218881813747503056253943286932954419704191570541989887127142) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 302 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 13 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (387 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_387 :
    recurrence5Scalar1Exceptional.coeff 387 =
      (((((8323774464341653217021035 * 10 ^ 70 +
        2258125457792182478862186939334011074497994028898844328480812011635718) * 10 ^ 70 +
        5176425765943017011764129786866385032242489279598146396651875693828695) * 10 ^ 70 +
        3922276732013584768014194190856634203044511518520700870780115286016861) * 10 ^ 70 +
        3148688700644817433401344694832353593762340808379727628544804144827637) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 303 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 12 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (388 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_388 :
    recurrence5Scalar1Exceptional.coeff 388 =
      -(((((1835934166351940622774946 * 10 ^ 70 +
        1603560265119847238834996801878481397234256482614124172105958804755143) * 10 ^ 70 +
        1353813928295573508581532623578754484834953870796737646516799518817584) * 10 ^ 70 +
        0603049726126178236165122539141835320901297979081051168277441305190441) * 10 ^ 70 +
        6216897087279296740068885570689196881820948574975238529251129344988854) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 304 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 11 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (389 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_389 :
    recurrence5Scalar1Exceptional.coeff 389 =
      (((((353362235131141899608932 * 10 ^ 70 +
        3587285260056535970802790409738203742359454890441518895663906438532916) * 10 ^ 70 +
        5945221429922441636894900675507071857261664237270263971132403026111380) * 10 ^ 70 +
        6171737509592854158086956380852824794353421164783016900223683969079318) * 10 ^ 70 +
        2629737797127215422111342394503932951450249108659553182995119720534681) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 305 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 10 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (390 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_390 :
    recurrence5Scalar1Exceptional.coeff 390 =
      -(((((55016026110522514658506 * 10 ^ 70 +
        4588014504598740161723642756140854333342064954829444724953862675483915) * 10 ^ 70 +
        8515106764223380616665566659337254750200112905706998694035734667593638) * 10 ^ 70 +
        1947097702510986423984655755803774023083599417666688785764192246603597) * 10 ^ 70 +
        8300564529472514312752817662706079447025787204570158598934315967277194) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 306 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 9 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (391 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_391 :
    recurrence5Scalar1Exceptional.coeff 391 =
      (((((5003451963078258005865 * 10 ^ 70 +
        7554227079761463544145948507793875438639328495388076674793295488074539) * 10 ^ 70 +
        1592206549898648441442532872686978871679622399248591968882010358257281) * 10 ^ 70 +
        2955492327260133560786004224203741833075598297798423670389708104038023) * 10 ^ 70 +
        6899057552548202610687098283141072162339498653158659429613672564924806) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 307 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 8 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (392 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_392 :
    recurrence5Scalar1Exceptional.coeff 392 =
      (((((720892982574318692369 * 10 ^ 70 +
        5470788943111916757223109203738335968180719226388132887373885190257901) * 10 ^ 70 +
        9868746600882371063785460791975714560721585446102131507991487064896347) * 10 ^ 70 +
        0184971488125567134662634537621900638321068159579946755457420986639945) * 10 ^ 70 +
        0138162314047374702660433816730580945951821002881100599008091804684375) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 308 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 7 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Exceptional_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence5ExceptionalProduct.coeff x * remainder7Coefficient1.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5C1_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Exceptional_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5ExceptionalProduct.coeff (379 + x) *
        remainder7Coefficient1.coeff (393 - (379 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5ExceptionalProduct_coeff_high (379 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Exceptional_coeff_393 :
    recurrence5Scalar1Exceptional.coeff 393 =
      -(((((557642553137562246535 * 10 ^ 70 +
        0853938513768944271709081104303797626175469369571667324216295569155702) * 10 ^ 70 +
        3905144994027826800761284562545470290582699625718085043271655805116703) * 10 ^ 70 +
        2533532990319559339537156470190278565534192121295264485101151521258053) * 10 ^ 70 +
        3230471710106911884389209705740779361040439696798220433274311185796441) : ℚ) := by
  unfold recurrence5Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 309 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 6 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Exceptional_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Exceptional_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
