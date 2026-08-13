/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart2Simp
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
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157

attribute [local simp]
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
  recurrence4B2_coeff_62
  recurrence4B2_coeff_63
  recurrence4B2_coeff_64
  recurrence4B2_coeff_65

attribute [local simp]
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
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
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

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar2Second_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (424 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_424 :
    recurrence4Scalar2Second.coeff 424 =
      ((((164780662462622325359469039247215453957851980 * 10 ^ 70 +
        6993993168091601198745062779730758675688019771000898123282393615767152) * 10 ^ 70 +
        0119010887467248644771306923763239303740723273759982486102277178930466) * 10 ^ 70 +
        8234818638546556832266596726315512813124737379839910846189868459780473) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (424 - x)) = _
  rw [show 425 = 78 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 27 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (425 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_425 :
    recurrence4Scalar2Second.coeff 425 =
      -((((45091874752896831696565080032115461851343095 * 10 ^ 70 +
        5506243649281618125254095443082391177486819458253197829926171836930714) * 10 ^ 70 +
        6055786000999109668603244157696424678342802275822942972069535453182003) * 10 ^ 70 +
        1370860580581611059408415071658233768921717605151288837349584352169271) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (425 - x)) = _
  rw [show 426 = 79 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 26 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (426 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_426 :
    recurrence4Scalar2Second.coeff 426 =
      ((((11661151472686361324143124985016066097628148 * 10 ^ 70 +
        8517015912903218637717649197978162574483559538336068904641412016044751) * 10 ^ 70 +
        2517583747271856718175680986767939352192931650217099088090755227197048) * 10 ^ 70 +
        5879067342013708205768061950002066363426663517931928068942321692847623) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (426 - x)) = _
  rw [show 427 = 80 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 25 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (427 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_427 :
    recurrence4Scalar2Second.coeff 427 =
      -((((2815398486048892420997387102843053534993141 * 10 ^ 70 +
        5864627804467813194235553135639605987789837900777301201683167722918938) * 10 ^ 70 +
        3964481960492609983508624280440562575043175497319595426368431378754361) * 10 ^ 70 +
        8924850015202088406960747784872960110533061482892630196951683867116354) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (427 - x)) = _
  rw [show 428 = 81 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 24 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (428 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_428 :
    recurrence4Scalar2Second.coeff 428 =
      ((((620991241758961415419300612100046813607585 * 10 ^ 70 +
        2923000125394812791595758966646478887559169374709211049650203569308821) * 10 ^ 70 +
        6356825140521699829236566370890511421134029433316111344540817824844737) * 10 ^ 70 +
        8906754151266977976583762078366671437779251452453538307608658916347412) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (428 - x)) = _
  rw [show 429 = 82 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 23 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (429 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_429 :
    recurrence4Scalar2Second.coeff 429 =
      -((((119546659637121521459535275379549356629284 * 10 ^ 70 +
        8340510300830570786608678905964087448818573174849157189497948855799985) * 10 ^ 70 +
        9991162850187627185060573850778356045161814905600693807327071270086670) * 10 ^ 70 +
        8773645478811146708720774200053301049842045978034491041726774427442553) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (429 - x)) = _
  rw [show 430 = 83 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 22 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (430 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_430 :
    recurrence4Scalar2Second.coeff 430 =
      ((((17613991774016421564791489360659172105406 * 10 ^ 70 +
        7592006031937224459448878574567959180262074590748371667547800967450513) * 10 ^ 70 +
        7368311948765229555536726401247456072048369284796315589195465243331638) * 10 ^ 70 +
        4506916667665925458485047556731623548367768171906697996926024296868392) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (430 - x)) = _
  rw [show 431 = 84 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 21 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (431 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_431 :
    recurrence4Scalar2Second.coeff 431 =
      -((((736659179960596210971055273221154910995 * 10 ^ 70 +
        8405457577191949975785200257649636748762255149893480971501491764717193) * 10 ^ 70 +
        4810461010592422297318075028453440455545804455696975872572975140030386) * 10 ^ 70 +
        7625448831141801475870016533059632336443028386561242857432045554508429) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (431 - x)) = _
  rw [show 432 = 85 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 20 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (432 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_432 :
    recurrence4Scalar2Second.coeff 432 =
      -((((793752699972652138849312554735857148663 * 10 ^ 70 +
        8239191679094930629357594476005628229952986025457661181013222126494417) * 10 ^ 70 +
        0917723449936951136133682229748840289547650213872354809976400157688377) * 10 ^ 70 +
        9497113500757767488991682639382460180778397244678174238933030348302498) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (432 - x)) = _
  rw [show 433 = 86 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 19 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (433 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_433 :
    recurrence4Scalar2Second.coeff 433 =
      ((((432069074281742271879655632309666337512 * 10 ^ 70 +
        9897868961801241256971758150669827749437701017363818131451203599832081) * 10 ^ 70 +
        0475195361686466203480004535365452737440599942718831278413338656186008) * 10 ^ 70 +
        7014017428966335463791093958635784663630480086430878469923997121109464) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (433 - x)) = _
  rw [show 434 = 87 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 18 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (434 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_434 :
    recurrence4Scalar2Second.coeff 434 =
      -((((157269419995314688245163554790850804194 * 10 ^ 70 +
        5978861148734566780107243987527739343945312174208525787277896222806190) * 10 ^ 70 +
        4255725849057223555165712509291840345350770379832335331720593740917857) * 10 ^ 70 +
        0437407965179544356453187287950608461124285418305705847337449531422468) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (434 - x)) = _
  rw [show 435 = 88 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 17 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (435 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_435 :
    recurrence4Scalar2Second.coeff 435 =
      ((((48045114306676685971388444993852890838 * 10 ^ 70 +
        5348943463908666922394316160663105726757399120329342904299199232768617) * 10 ^ 70 +
        3373915204981488142031699533160285835324605257797959260720441013646039) * 10 ^ 70 +
        7622626588515093892830201110291475586981152259721980035486567937187234) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (435 - x)) = _
  rw [show 436 = 89 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 16 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (436 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_436 :
    recurrence4Scalar2Second.coeff 436 =
      -((((13110163102480108470102194290624099876 * 10 ^ 70 +
        6530334581133266280905265841499385945872384248132658688966869891036156) * 10 ^ 70 +
        4883353507748966475121865969792400453845682564329831035589756131770337) * 10 ^ 70 +
        3273550048760452641164607862057403184267956399443009915115562264566203) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (436 - x)) = _
  rw [show 437 = 90 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 15 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (437 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_437 :
    recurrence4Scalar2Second.coeff 437 =
      ((((3276595342382490564917959221431736350 * 10 ^ 70 +
        0270922953434187614560274914769352693680711186087642323016725636492882) * 10 ^ 70 +
        3348473445090886274208026457243220302989497479114889073057187881159806) * 10 ^ 70 +
        6787994257826034028769677426123830086825551779425382295259167852059979) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (437 - x)) = _
  rw [show 438 = 91 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 14 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (438 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_438 :
    recurrence4Scalar2Second.coeff 438 =
      -((((758805710912035408401982118382466577 * 10 ^ 70 +
        0742871833230143851908015715567838260879614249532280391842108825343196) * 10 ^ 70 +
        5138046388921479206264536764111420361253138173256998420857356855536065) * 10 ^ 70 +
        7390794053573933225610069627933086211875607385205608274723438242754443) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (438 - x)) = _
  rw [show 439 = 92 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 13 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (439 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_439 :
    recurrence4Scalar2Second.coeff 439 =
      ((((163673537480066441041870062860359513 * 10 ^ 70 +
        9316582351691554244125156356845915073933303710301886718946039918564984) * 10 ^ 70 +
        1254446479811114139813892099460676909142680573242091056060377843290819) * 10 ^ 70 +
        6159858072120732924297296161690097185634607710654018119116809305855942) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (439 - x)) = _
  rw [show 440 = 93 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 12 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (440 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_440 :
    recurrence4Scalar2Second.coeff 440 =
      -((((32926429242139503608579280162845895 * 10 ^ 70 +
        6185737585976596141269239239420621505288516517831243606420065727281216) * 10 ^ 70 +
        7176761645424310299215159786645174576234873270616821840107145854151331) * 10 ^ 70 +
        2050869138564947039278922817822119249011296903343753610632155254199234) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (440 - x)) = _
  rw [show 441 = 94 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 11 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (441 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_441 :
    recurrence4Scalar2Second.coeff 441 =
      ((((6167667844965404942067959332992127 * 10 ^ 70 +
        1036629597624106339108317393936549289880894172085472520735036252567079) * 10 ^ 70 +
        6819253012154449897885079785785710732154409311123918809485742594116738) * 10 ^ 70 +
        5960989432368620863904942291725923591708549698453699981843385737995593) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (441 - x)) = _
  rw [show 442 = 95 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 10 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (442 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_442 :
    recurrence4Scalar2Second.coeff 442 =
      -((((1070726584205785044738918285234268 * 10 ^ 70 +
        9566740882179156074471474235253017559826996635593151330336840512824853) * 10 ^ 70 +
        7359870918888888086666103797443017540700860311832927009167908444467089) * 10 ^ 70 +
        3535476901498395914280213961336283607734260839465925647853767138963367) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (442 - x)) = _
  rw [show 443 = 96 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 9 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (443 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_443 :
    recurrence4Scalar2Second.coeff 443 =
      ((((170765371026368260757174483901687 * 10 ^ 70 +
        6277590127268297728130993880076773023211580875544172951364938627592862) * 10 ^ 70 +
        7727643971677004602595715885765760026745860050054020019097796517072066) * 10 ^ 70 +
        9783078990677835504537998483905427077525162132568124243347491430795401) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (443 - x)) = _
  rw [show 444 = 97 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 8 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (444 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_444 :
    recurrence4Scalar2Second.coeff 444 =
      -((((24626309954683550120593863822881 * 10 ^ 70 +
        3519161510661082259691506989512776790661498390622022033555395958829216) * 10 ^ 70 +
        5728112861651240801987696108203551761730283918102900628207066025989403) * 10 ^ 70 +
        3215642569582519772720162272539774870281985019878501523958585155137874) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (444 - x)) = _
  rw [show 445 = 98 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 7 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (445 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_445 :
    recurrence4Scalar2Second.coeff 445 =
      ((((3113368322824740457758185963490 * 10 ^ 70 +
        7388962727859133498085588895518725765539506235991213064196750039691347) * 10 ^ 70 +
        4461770126352647277804038352329210200997627978860851883422018338283711) * 10 ^ 70 +
        8089808359004994773649919904509265655770730414880474553536184136405479) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (445 - x)) = _
  rw [show 446 = 99 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 6 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (446 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_446 :
    recurrence4Scalar2Second.coeff 446 =
      -((((320558172272480639370358133474 * 10 ^ 70 +
        4327671519813289745625890646010792027478088314734710295707847329794169) * 10 ^ 70 +
        5351960922296548739866092506097838383464101882707374187824816740968145) * 10 ^ 70 +
        0152793404221969409614841836821402476311274723700008624428465352411524) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (446 - x)) = _
  rw [show 447 = 100 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 5 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (447 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_447 :
    recurrence4Scalar2Second.coeff 447 =
      ((((20351041710268114659293878274 * 10 ^ 70 +
        6167025714354071385230514546713990454448702456671928919251355264664556) * 10 ^ 70 +
        2457995219704911745638239012182424574896275621670866941426704117845449) * 10 ^ 70 +
        7390852130316816938908301285537536464620292834771840364606052619876713) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (447 - x)) = _
  rw [show 448 = 101 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 4 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (448 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_448 :
    recurrence4Scalar2Second.coeff 448 =
      ((((1231373220293710108350461824 * 10 ^ 70 +
        6953375222458084894599165201827464434666928992370991564119849869301902) * 10 ^ 70 +
        1776061720377478655734952189959451485389205297104196349091512825871053) * 10 ^ 70 +
        6272458610600658096280846591692817603796560660371330746758227868058382) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (448 - x)) = _
  rw [show 449 = 102 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 3 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (449 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_449 :
    recurrence4Scalar2Second.coeff 449 =
      -((((722419293867099086142045695 * 10 ^ 70 +
        8374216141205462041942905541548376359458796901003096123674880344532703) * 10 ^ 70 +
        2710306294568467991784753848438812775005807481835900080436968850448234) * 10 ^ 70 +
        7933942703113751334239989292108242213021908820440826333141643150409738) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (449 - x)) = _
  rw [show 450 = 103 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 2 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Second_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (450 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_450 :
    recurrence4Scalar2Second.coeff 450 =
      ((((158344584194332632583826392 * 10 ^ 70 +
        1080974622447210442725747545438895670828225402383643312796191054741149) * 10 ^ 70 +
        7411609808754016936128479160569148504424935151234412907830555275253930) * 10 ^ 70 +
        1379727851671197507969849406774010381262122845195896004265143456733837) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (450 - x)) = _
  rw [show 451 = 104 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 283 = 1 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
