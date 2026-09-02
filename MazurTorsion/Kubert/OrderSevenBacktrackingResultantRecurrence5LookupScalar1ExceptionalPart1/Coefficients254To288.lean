/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
