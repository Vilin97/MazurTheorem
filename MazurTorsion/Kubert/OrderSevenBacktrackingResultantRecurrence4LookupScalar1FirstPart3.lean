/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163

attribute [local simp]
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_60
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92

attribute [local simp]
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_210
  recurrence4B3A4_coeff_211
  recurrence4B3A4_coeff_212
  recurrence4B3A4_coeff_213
  recurrence4B3A4_coeff_214
  recurrence4B3A4_coeff_215
  recurrence4B3A4_coeff_216
  recurrence4B3A4_coeff_217
  recurrence4B3A4_coeff_218
  recurrence4B3A4_coeff_219
  recurrence4B3A4_coeff_220
  recurrence4B3A4_coeff_221
  recurrence4B3A4_coeff_222
  recurrence4B3A4_coeff_223
  recurrence4B3A4_coeff_224
  recurrence4B3A4_coeff_225
  recurrence4B3A4_coeff_226
  recurrence4B3A4_coeff_227
  recurrence4B3A4_coeff_228
  recurrence4B3A4_coeff_229
  recurrence4B3A4_coeff_230
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_240
  recurrence4B3A4_coeff_241
  recurrence4B3A4_coeff_242
  recurrence4B3A4_coeff_243
  recurrence4B3A4_coeff_244
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251
  recurrence4B3A4_coeff_252
  recurrence4B3A4_coeff_253
  recurrence4B3A4_coeff_254
  recurrence4B3A4_coeff_255
  recurrence4B3A4_coeff_256
  recurrence4B3A4_coeff_257
  recurrence4B3A4_coeff_258
  recurrence4B3A4_coeff_259
  recurrence4B3A4_coeff_260
  recurrence4B3A4_coeff_261
  recurrence4B3A4_coeff_262
  recurrence4B3A4_coeff_263
  recurrence4B3A4_coeff_264

attribute [local simp]
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
  recurrence4B3A4_coeff_275
  recurrence4B3A4_coeff_276
  recurrence4B3A4_coeff_277
  recurrence4B3A4_coeff_278
  recurrence4B3A4_coeff_279
  recurrence4B3A4_coeff_280
  recurrence4B3A4_coeff_281
  recurrence4B3A4_coeff_282
  recurrence4B3A4_coeff_283
  recurrence4B3A4_coeff_284
  recurrence4B3A4_coeff_285
  recurrence4B3A4_coeff_286
  recurrence4B3A4_coeff_287
  recurrence4B3A4_coeff_288
  recurrence4B3A4_coeff_289
  recurrence4B3A4_coeff_290
  recurrence4B3A4_coeff_291
  recurrence4B3A4_coeff_292
  recurrence4B3A4_coeff_293
  recurrence4B3A4_coeff_294
  recurrence4B3A4_coeff_295
  recurrence4B3A4_coeff_296
  recurrence4B3A4_coeff_297
  recurrence4B3A4_coeff_298
  recurrence4B3A4_coeff_299
  recurrence4B3A4_coeff_300
  recurrence4B3A4_coeff_301
  recurrence4B3A4_coeff_302
  recurrence4B3A4_coeff_303
  recurrence4B3A4_coeff_304
  recurrence4B3A4_coeff_305
  recurrence4B3A4_coeff_306
  recurrence4B3A4_coeff_307
  recurrence4B3A4_coeff_308
  recurrence4B3A4_coeff_309
  recurrence4B3A4_coeff_310
  recurrence4B3A4_coeff_311
  recurrence4B3A4_coeff_312
  recurrence4B3A4_coeff_313
  recurrence4B3A4_coeff_314
  recurrence4B3A4_coeff_315
  recurrence4B3A4_coeff_316
  recurrence4B3A4_coeff_317
  recurrence4B3A4_coeff_318
  recurrence4B3A4_coeff_319
  recurrence4B3A4_coeff_320
  recurrence4B3A4_coeff_321
  recurrence4B3A4_coeff_322
  recurrence4B3A4_coeff_323
  recurrence4B3A4_coeff_324
  recurrence4B3A4_coeff_325
  recurrence4B3A4_coeff_326
  recurrence4B3A4_coeff_327
  recurrence4B3A4_coeff_328

attribute [local simp]
  recurrence4B3A4_coeff_329
  recurrence4B3A4_coeff_330
  recurrence4B3A4_coeff_331
  recurrence4B3A4_coeff_332
  recurrence4B3A4_coeff_333
  recurrence4B3A4_coeff_334
  recurrence4B3A4_coeff_335
  recurrence4B3A4_coeff_336
  recurrence4B3A4_coeff_337
  recurrence4B3A4_coeff_338
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar1First_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (384 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (384 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_384 :
    recurrence4Scalar1First.coeff 384 =
      ((((12204900858576666694737154951476219397819654870536717293851060741 * 10 ^ 70 +
        6881646411325071197957329876219835063819754664723132719285796063202065) * 10 ^ 70 +
        9527548674390232702346411693234258242982057431921552045833874266965061) * 10 ^ 70 +
        4255087695874362596061739889810834105226769509754870429124356215542834) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (384 - x)) = _
  rw [show 385 = 42 +
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
    rw [show 215 = 7 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (385 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (385 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_385 :
    recurrence4Scalar1First.coeff 385 =
      -((((4499223418280417864160162119776585281656740311017334447491356044 * 10 ^ 70 +
        4362737174375632248945310625381846738621049383497936909318814057023309) * 10 ^ 70 +
        8291776068588762896816709313009856621092985181588158077938983838165387) * 10 ^ 70 +
        1276772140421004618803539750058967870610496793166151012463552268310455) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (385 - x)) = _
  rw [show 386 = 43 +
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
    rw [show 215 = 6 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (386 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (386 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_386 :
    recurrence4Scalar1First.coeff 386 =
      ((((1532548927771914364350050273420006236771027678498183469871711301 * 10 ^ 70 +
        1292111233981291570804998055921240969567063578235352908817717752860451) * 10 ^ 70 +
        3046420367942403368007097513521918803752606228720354431846601218806237) * 10 ^ 70 +
        1292721351874295988864120794611272123628269050577044224014448741572249) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (386 - x)) = _
  rw [show 387 = 44 +
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
    rw [show 215 = 5 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (387 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (387 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_387 :
    recurrence4Scalar1First.coeff 387 =
      -((((483099392062704180343136605588131793160929468766700743940463613 * 10 ^ 70 +
        3558098855630453231452442663869838858692089419522180092586570707641297) * 10 ^ 70 +
        2936685130161567294503835031168176938763185433399481699192142752743693) * 10 ^ 70 +
        8867927834814581868215665912495478882487819286960384485488159210659513) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (387 - x)) = _
  rw [show 388 = 45 +
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
    rw [show 215 = 4 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (388 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (388 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_388 :
    recurrence4Scalar1First.coeff 388 =
      ((((139572627525093435548583520225923792810861683427608001650673873 * 10 ^ 70 +
        7500081173575775768783051800676363596675511433727936830525474737982392) * 10 ^ 70 +
        1053152500505410089353057756323355428818928388896097095887791428883558) * 10 ^ 70 +
        7243781450096924080845656252154848500462072231803800371151442144265923) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (388 - x)) = _
  rw [show 389 = 46 +
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
    rw [show 215 = 3 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (389 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (389 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_389 :
    recurrence4Scalar1First.coeff 389 =
      -((((35923614105550759581598517760005949077534492713720341466932895 * 10 ^ 70 +
        5786307847260609024483200931157424414495072997436058503160878046580582) * 10 ^ 70 +
        1638153196688318731777644825194126638762818936475405673957130679798981) * 10 ^ 70 +
        6369946816543268957795304431159008500505864652715187531210426544520824) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (389 - x)) = _
  rw [show 390 = 47 +
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
    rw [show 215 = 2 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (390 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (390 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_390 :
    recurrence4Scalar1First.coeff 390 =
      ((((7602986761551684239757185977805075163748858620729669162437853 * 10 ^ 70 +
        7905209683270755349055864186170230280140182657289112947246668778369527) * 10 ^ 70 +
        1970072689583188178903915197592874272992858140404025914575149847815615) * 10 ^ 70 +
        1290657597637193789283437350283383386859091341662993540469270972992936) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (390 - x)) = _
  rw [show 391 = 48 +
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
    rw [show 215 = 1 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (391 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (391 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_391 :
    recurrence4Scalar1First.coeff 391 =
      -((((921424972767487075453386005621359223165351457758210733394408 * 10 ^ 70 +
        1215679436247451422953473907405534334868215793941579797295682893051913) * 10 ^ 70 +
        4798497727618112862698648028492107313031912129402209959272843405033477) * 10 ^ 70 +
        5966568975637369551282784261821270594931796776211914109119859625268631) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (391 - x)) = _
  rw [show 392 = 49 +
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
  rw [recurrence4Scalar1First_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (392 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (392 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_392 :
    recurrence4Scalar1First.coeff 392 =
      -((((240288852949163725845436687784898501433570010968313113766330 * 10 ^ 70 +
        4374200957909788394994343205794167801401365582451470880965526743557946) * 10 ^ 70 +
        0642020357812775836959858628079778725055552597971323109648165135033114) * 10 ^ 70 +
        0348969679367361502496730899629825368392844126562547557742671374632647) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (392 - x)) = _
  rw [show 393 = 50 +
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
    rw [show 247 = 31 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (393 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (393 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_393 :
    recurrence4Scalar1First.coeff 393 =
      ((((253384362893700793159340416274100552998192038688220713719702 * 10 ^ 70 +
        7612957151719692375089356932687730460970009109898350794793547438055999) * 10 ^ 70 +
        4572878041743270051399647388806988988994844840010216571525909534648242) * 10 ^ 70 +
        3007051754591920895358632784616513511488713485067186748085132287197962) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (393 - x)) = _
  rw [show 394 = 51 +
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
    rw [show 247 = 30 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (394 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (394 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_394 :
    recurrence4Scalar1First.coeff 394 =
      -((((136037646539690565497043103647399562389398443151899500840474 * 10 ^ 70 +
        2938070383197165619170766742590892414262748701135558648264373287194681) * 10 ^ 70 +
        4865397364908982488527260176067621035193971051774000047329596190339477) * 10 ^ 70 +
        3010243773347162526773707144606282629473829787378414498850519215585817) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (394 - x)) = _
  rw [show 395 = 52 +
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
    rw [show 247 = 29 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (395 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (395 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_395 :
    recurrence4Scalar1First.coeff 395 =
      ((((59868053132371243435650693997577469416931415015996133529573 * 10 ^ 70 +
        9083196518053629317408625371452427087800011209456566936178748223034043) * 10 ^ 70 +
        5556315776349109958629075050149529043331272936167880084930376375832317) * 10 ^ 70 +
        9367619048274364506499611554510170354481266726475326763006602392500008) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (395 - x)) = _
  rw [show 396 = 53 +
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
    rw [show 247 = 28 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (396 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (396 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_396 :
    recurrence4Scalar1First.coeff 396 =
      -((((23847436307716200588026251666996068403504758619446519421303 * 10 ^ 70 +
        1220091653244842449583184898083685429297726192991542808162446080650758) * 10 ^ 70 +
        4258620590754922290076891433320541483601972115683624563679710970882408) * 10 ^ 70 +
        5854340270202101347829971697514414234482023382630253387495686985289960) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (396 - x)) = _
  rw [show 397 = 54 +
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
    rw [show 247 = 27 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (397 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (397 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_397 :
    recurrence4Scalar1First.coeff 397 =
      ((((8947107138823702432002772981394590344945355944788697747223 * 10 ^ 70 +
        7844095535791731296710140331683487960966144887182251238501308942824938) * 10 ^ 70 +
        6754257398441178524741015724065530252151551655616459610298142379697800) * 10 ^ 70 +
        7169466261701266894199714491723999696112907623713519267491873298054019) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (397 - x)) = _
  rw [show 398 = 55 +
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
    rw [show 247 = 26 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (398 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (398 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_398 :
    recurrence4Scalar1First.coeff 398 =
      -((((3227328677516584126420021757434369295218821030095435190569 * 10 ^ 70 +
        8920602194745796819194006771742096724212531109018668266314800721949658) * 10 ^ 70 +
        7859632260945548485902251955750605797589035624882853312487172164141358) * 10 ^ 70 +
        6761327024524279629275135629074222934146800181333903582405114646190232) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (398 - x)) = _
  rw [show 399 = 56 +
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
    rw [show 247 = 25 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (399 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (399 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_399 :
    recurrence4Scalar1First.coeff 399 =
      ((((1131995939189880608631948282698584141125431535993822011547 * 10 ^ 70 +
        8864052363242655984073310343612141083170919957506548035882463312950696) * 10 ^ 70 +
        3413216870247539925992706923069916660745463810426913785605321489579387) * 10 ^ 70 +
        1889739814147164555620896271291001130792292111070139530583448020740487) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (399 - x)) = _
  rw [show 400 = 57 +
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
    rw [show 247 = 24 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (400 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (400 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_400 :
    recurrence4Scalar1First.coeff 400 =
      -((((388145498434093369312851364133658550900020402970864321649 * 10 ^ 70 +
        7822138527263511545590238640020127461778341549127349545746254945596142) * 10 ^ 70 +
        8006948097354716267837779000810388985555709350668572917346302306831757) * 10 ^ 70 +
        2324877907631799846754320915935357767493774694074872891717040190546778) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (400 - x)) = _
  rw [show 401 = 58 +
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
    rw [show 247 = 23 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (401 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (401 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_401 :
    recurrence4Scalar1First.coeff 401 =
      ((((130181584754645246680306352054577559646363044682260577636 * 10 ^ 70 +
        2635220551912088632344896090302244988910924993202079586007622076990383) * 10 ^ 70 +
        3878799517523248650609721466856966029208576776022724742990548486868328) * 10 ^ 70 +
        5851234307197813391966741905867942031838254411986049860290723226432025) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (401 - x)) = _
  rw [show 402 = 59 +
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
    rw [show 247 = 22 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (402 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (402 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_402 :
    recurrence4Scalar1First.coeff 402 =
      -((((42566862319890955177280898597346430305921129461327201423 * 10 ^ 70 +
        3680695732861283931247205292399748186731725310989498284878224418815414) * 10 ^ 70 +
        3224604189000073991459318733031865288379447051124065705317393299229317) * 10 ^ 70 +
        5056371324699818531480013142565826878725632292944066996043945954907065) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (402 - x)) = _
  rw [show 403 = 60 +
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
    rw [show 247 = 21 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (403 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (403 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_403 :
    recurrence4Scalar1First.coeff 403 =
      ((((13479491447253963470567951215560672626926432419154161397 * 10 ^ 70 +
        2556464843042046134001547369330073207759830569792592303617521594630204) * 10 ^ 70 +
        3562160870291514794184362583404019522346231876152682315306207913244312) * 10 ^ 70 +
        7698687787352524527161459595903261082647432452936598447852792709657628) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (403 - x)) = _
  rw [show 404 = 61 +
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
    rw [show 247 = 20 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (404 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (404 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_404 :
    recurrence4Scalar1First.coeff 404 =
      -((((4092656204421569061614864142198881440423639989426437246 * 10 ^ 70 +
        0347902007175323113449875892232398434444074802741906257191660294021949) * 10 ^ 70 +
        0927607673198291705479288226954199778251265145368090914132169952580750) * 10 ^ 70 +
        5899434468497932066638968565131939823438458653781305275935215068180244) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (404 - x)) = _
  rw [show 405 = 62 +
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
    rw [show 247 = 19 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (405 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (405 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_405 :
    recurrence4Scalar1First.coeff 405 =
      ((((1173826241651622832615576570713860203862874943232834223 * 10 ^ 70 +
        0849619705468965439891400611410237787085396111301836427016167389466612) * 10 ^ 70 +
        4331282801285834863448460485247240466712152998277920295753520325289842) * 10 ^ 70 +
        7949431728819978443103109829550116023450022920784835336381393480943626) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (405 - x)) = _
  rw [show 406 = 63 +
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
    rw [show 247 = 18 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (406 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (406 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_406 :
    recurrence4Scalar1First.coeff 406 =
      -((((310192905256873961392066397237511988185410028819908267 * 10 ^ 70 +
        0227620716647283687328095068577816011803292493913815317394406326918721) * 10 ^ 70 +
        9386761854886530729883321673982009335981838607273086269917313997233620) * 10 ^ 70 +
        7316193516319007330970346438348446028936727167238488781641606909505859) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (406 - x)) = _
  rw [show 407 = 64 +
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
    rw [show 247 = 17 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (407 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (407 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_407 :
    recurrence4Scalar1First.coeff 407 =
      ((((71667534006198999390806729955123774173709766185027814 * 10 ^ 70 +
        6602450656779896079845692783626376661551071701748046480739342418711009) * 10 ^ 70 +
        3741156098936704247851375851585787129811100064110279735093017344538483) * 10 ^ 70 +
        9827395365369670073880213559599275240092163379357609364196157129259423) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (407 - x)) = _
  rw [show 408 = 65 +
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
    rw [show 247 = 16 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (408 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (408 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_408 :
    recurrence4Scalar1First.coeff 408 =
      -((((12314685739099620975860896360379613234942106121251067 * 10 ^ 70 +
        0491203118050764144335905889914474969898148244687878621385752682179587) * 10 ^ 70 +
        5952939596071997627138389100751323271957193756800517959646629631770366) * 10 ^ 70 +
        7129285628518049532729208439036854129286319510845475609475835077812672) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (408 - x)) = _
  rw [show 409 = 66 +
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
    rw [show 247 = 15 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (409 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (409 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_409 :
    recurrence4Scalar1First.coeff 409 =
      ((((126094030961639835084911499362699075373938030502806 * 10 ^ 70 +
        3563238178622721904475602054103387314463145290516033711046602745017299) * 10 ^ 70 +
        7539670967817371839203612533101493168624223714557738903482192024788187) * 10 ^ 70 +
        4526198348160514746041733769019642398728004828790494919343158444286335) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (409 - x)) = _
  rw [show 410 = 67 +
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
    rw [show 247 = 14 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (410 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (410 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_410 :
    recurrence4Scalar1First.coeff 410 =
      ((((1261144996264465699241456232569362526294220749464114 * 10 ^ 70 +
        4854385389744970880949666450204246449449169203604411257525630944836748) * 10 ^ 70 +
        4790700044655010580162247542678015723527386959575974079805027412617216) * 10 ^ 70 +
        4318531524001897459105826465684887101500507659910374017998294478392726) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (410 - x)) = _
  rw [show 411 = 68 +
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
    rw [show 247 = 13 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (411 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (411 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_411 :
    recurrence4Scalar1First.coeff 411 =
      -((((832578326569442170203503428575288387019851055342935 * 10 ^ 70 +
        6856756299609761820769159537239681622687106863762339320078117448474967) * 10 ^ 70 +
        2563168898785292935582501889440687945449707912114732765199287448146933) * 10 ^ 70 +
        0883044625708209621345023896949678093537868960049337106467251475110676) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (411 - x)) = _
  rw [show 412 = 69 +
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
    rw [show 247 = 12 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (412 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (412 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_412 :
    recurrence4Scalar1First.coeff 412 =
      ((((405633917461658529955106442537298888721876050988260 * 10 ^ 70 +
        6257194225674942751135934100848406812589047858396635543794544940356708) * 10 ^ 70 +
        7390957701219051321351853312988387545724416797141841489728819012393827) * 10 ^ 70 +
        1229558685573845029953359347103678028825589066741295891755389239293519) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (412 - x)) = _
  rw [show 413 = 70 +
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
    rw [show 247 = 11 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (413 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (413 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_413 :
    recurrence4Scalar1First.coeff 413 =
      -((((175129248352031950367568626172171850928915623248721 * 10 ^ 70 +
        9323729360025516027638882802661668953405589468981055750737104427484301) * 10 ^ 70 +
        8303728918441634563239204852479786879912413781802739131557343299710762) * 10 ^ 70 +
        5871114376928745671420476601367723195428334033484824627494671584863767) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (413 - x)) = _
  rw [show 414 = 71 +
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
    rw [show 247 = 10 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (414 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (414 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_414 :
    recurrence4Scalar1First.coeff 414 =
      ((((71068665389949514774254619344485899375979720817465 * 10 ^ 70 +
        3111637039350829058054046948681500794727183244202171359731212521719991) * 10 ^ 70 +
        2770847764697588608509920474760194134993130960998318190966373292745943) * 10 ^ 70 +
        3165343465221690722454825095828938585059153075698182973773857612590818) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (414 - x)) = _
  rw [show 415 = 72 +
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
    rw [show 247 = 9 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (415 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (415 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_415 :
    recurrence4Scalar1First.coeff 415 =
      -((((27834010972262706447306443565527750713851726815993 * 10 ^ 70 +
        4133609007963615917467710303419079540270712710930483618766780123395516) * 10 ^ 70 +
        2696040407028547209898335527644601589311916863847932007139038705699973) * 10 ^ 70 +
        8950021746110710383200202247763509428473440492276431649674828212000784) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (415 - x)) = _
  rw [show 416 = 73 +
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
    rw [show 247 = 8 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (416 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (416 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_416 :
    recurrence4Scalar1First.coeff 416 =
      ((((10653112188201490388910657403193418904764698526092 * 10 ^ 70 +
        0612110698690949008501865573893788742986459144955735726696502003951116) * 10 ^ 70 +
        5308056587210227364645468210747603974288321514533590336392471957885177) * 10 ^ 70 +
        0842497298834312224078930171073431998457333750963793811236535539827378) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (416 - x)) = _
  rw [show 417 = 74 +
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
    rw [show 247 = 7 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (417 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (417 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_417 :
    recurrence4Scalar1First.coeff 417 =
      -((((4002859509429166695040939599159492825706589709259 * 10 ^ 70 +
        3481227222484025945627106683104168859787411790311966289481892026925077) * 10 ^ 70 +
        5769560478910099862368040303576388503218636237060475426569604787497709) * 10 ^ 70 +
        4931285865364798940893362528886445851591948272307119555214641417809227) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (417 - x)) = _
  rw [show 418 = 75 +
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
    rw [show 247 = 6 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (418 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (418 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_418 :
    recurrence4Scalar1First.coeff 418 =
      ((((1476118563612925448975140044625345148880346186120 * 10 ^ 70 +
        3933310222608179193026554143855234070286079965843832005176473390401412) * 10 ^ 70 +
        3082751439976855163773611764408144687744804335590214848706389799418353) * 10 ^ 70 +
        1899756070116663489074695764128763128769571882720214503484222078575637) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (418 - x)) = _
  rw [show 419 = 76 +
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
    rw [show 247 = 5 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (419 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (419 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_419 :
    recurrence4Scalar1First.coeff 419 =
      -((((532546780661737510224264188479387132480063730469 * 10 ^ 70 +
        2819087271139037001550995347824746800643383076558265203465190960967051) * 10 ^ 70 +
        5533560481734277587649504405380300235566348436113493594580882647409519) * 10 ^ 70 +
        1488000706519842988414620598101744853071426735076472369210396071926393) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (419 - x)) = _
  rw [show 420 = 77 +
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
    rw [show 247 = 4 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (420 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (420 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_420 :
    recurrence4Scalar1First.coeff 420 =
      ((((187112849634670669710045347961181346738007937296 * 10 ^ 70 +
        1527235723999603459510087300264916719232134010882367529520785873928107) * 10 ^ 70 +
        5318542909321838203270407022891920225746276688190440127581402107129491) * 10 ^ 70 +
        9396116421564469112899803386568638689148028235025784665207760682111662) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (420 - x)) = _
  rw [show 421 = 78 +
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
    rw [show 247 = 3 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (421 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (421 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_421 :
    recurrence4Scalar1First.coeff 421 =
      -((((63702355301096879307293242674104702974047304586 * 10 ^ 70 +
        2189859477735125343932496233115402666691905230304474247774730783343492) * 10 ^ 70 +
        6238393883261825228990307175905195964741283177366025028708439281983611) * 10 ^ 70 +
        5333534936561251204821483599877389342653417353469474104284858685847814) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (421 - x)) = _
  rw [show 422 = 79 +
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
    rw [show 247 = 2 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (422 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (422 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_422 :
    recurrence4Scalar1First.coeff 422 =
      ((((20903874329547241551944477327373204386858295987 * 10 ^ 70 +
        7639778737365994564809643393999002780174397265545545109780657600427627) * 10 ^ 70 +
        0576670603025791184416795136359306972836415343396963965323987304969569) * 10 ^ 70 +
        1984251044102986328033610785066826533091749347192295708461225691260931) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (422 - x)) = _
  rw [show 423 = 80 +
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
    rw [show 247 = 1 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (423 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (423 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_423 :
    recurrence4Scalar1First.coeff 423 =
      -((((6574931811378281647287150358130890759458684964 * 10 ^ 70 +
        2644728759879814005306634316018057674089370833134505757886843782808686) * 10 ^ 70 +
        0957051248550719409674419624413264148886686746761880617575433166937306) * 10 ^ 70 +
        5379540712464073059522640782462244013888934855222229250599461691385365) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (423 - x)) = _
  rw [show 424 = 81 +
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
  rw [recurrence4Scalar1First_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (424 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (424 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_424 :
    recurrence4Scalar1First.coeff 424 =
      ((((1969408069649551648669760350322372556059481701 * 10 ^ 70 +
        7457321776674618216754865223112037122471871356004901198536798706950343) * 10 ^ 70 +
        0628949785018180332918100174176348607634244294087994802161048368695354) * 10 ^ 70 +
        7684468788492534130736881286340706758568735339831459935338028642328335) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (424 - x)) = _
  rw [show 425 = 82 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 31 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (425 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (425 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_425 :
    recurrence4Scalar1First.coeff 425 =
      -((((556993050167933241975068705441896131132744936 * 10 ^ 70 +
        7874025919768391511892391673726626029342757745222840684741696779943335) * 10 ^ 70 +
        4879995749888719256801526529517725346394468102677265448383214406899683) * 10 ^ 70 +
        6866683335767896737008278033354764573596503529890106678596197851808715) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (425 - x)) = _
  rw [show 426 = 83 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 30 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (426 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (426 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_426 :
    recurrence4Scalar1First.coeff 426 =
      ((((146818243655961183929081422081159288334296316 * 10 ^ 70 +
        1232793750179516738566177621066918319901299315189813460958490334872471) * 10 ^ 70 +
        7028427543965112671030972013545318661955081735247541668186706943588746) * 10 ^ 70 +
        0276433936169911095187710135509397277941009065668364790512493812847076) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (426 - x)) = _
  rw [show 427 = 84 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 29 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (427 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (427 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_427 :
    recurrence4Scalar1First.coeff 427 =
      -((((35241793777768178260823436641252756735768406 * 10 ^ 70 +
        2259808898090659142176180203951696777790485574783715026061855339877771) * 10 ^ 70 +
        0446204906840038030225491585500861297434379932996907671828241395976807) * 10 ^ 70 +
        8690893496861929865666039025171121890083560730701544563293992041661860) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (427 - x)) = _
  rw [show 428 = 85 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 28 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (428 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (428 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_428 :
    recurrence4Scalar1First.coeff 428 =
      ((((7325061108222872675037770520055189708283993 * 10 ^ 70 +
        5807302855314584089624889951576483985685278119344422509335845781324231) * 10 ^ 70 +
        2032762213538020225009186279631056851644701748260096917996736362637626) * 10 ^ 70 +
        3323458566730419172708948740876950078136155823339629447982376322543370) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (428 - x)) = _
  rw [show 429 = 86 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 27 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (429 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (429 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_429 :
    recurrence4Scalar1First.coeff 429 =
      -((((1130004530642996826581922239117057477063746 * 10 ^ 70 +
        3564265967269146680637668517209474866626395314879361943436831207812383) * 10 ^ 70 +
        4774013190024858324426789873932875597446292154805267664378242422861012) * 10 ^ 70 +
        5488696314079257376469923623659357150203392793859860516326568092267992) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (429 - x)) = _
  rw [show 430 = 87 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 26 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (430 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (430 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_430 :
    recurrence4Scalar1First.coeff 430 =
      ((((21053159365973591235619219175767840491349 * 10 ^ 70 +
        6335475446623151487780580733072541228141212595651040009417615719950922) * 10 ^ 70 +
        9725109152225720311987235096160575099802467396423817091132733968759946) * 10 ^ 70 +
        4669404413082969540221680011944962880406000894933604329615817666811707) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (430 - x)) = _
  rw [show 431 = 88 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 25 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (431 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (431 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_431 :
    recurrence4Scalar1First.coeff 431 =
      ((((79599620568323515975148767013230774199049 * 10 ^ 70 +
        9502493399342054907121272448589060601860189957479814247313628706733997) * 10 ^ 70 +
        1151765277197106308599427188146878363970352087917324862514098139665005) * 10 ^ 70 +
        2260084616645496212734756360397814449279092543928143419367725043245799) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (431 - x)) = _
  rw [show 432 = 89 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 24 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (432 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (432 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_432 :
    recurrence4Scalar1First.coeff 432 =
      -((((44671674980263173513733185486935342783545 * 10 ^ 70 +
        9381185907282987752361044073798624666566161192986342912371165627309212) * 10 ^ 70 +
        3043269643145482557647032966017402695487434106821007120634159206121337) * 10 ^ 70 +
        4868800498700953537236501411222313976546167961514819607211384815982394) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (432 - x)) = _
  rw [show 433 = 90 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 23 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (433 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (433 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_433 :
    recurrence4Scalar1First.coeff 433 =
      ((((17736319496537408058441458301195324149033 * 10 ^ 70 +
        6061763322005982918058180198878224427399243807510649014776564193363263) * 10 ^ 70 +
        8513735776582230748219481107742809959159029074478528618369770887897855) * 10 ^ 70 +
        4485318229627350924813019901026023698896254081551764280758523479364174) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (433 - x)) = _
  rw [show 434 = 91 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 22 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (434 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (434 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_434 :
    recurrence4Scalar1First.coeff 434 =
      -((((6010647907249748962183151215881388220065 * 10 ^ 70 +
        3269696307554027508165852713062984114639707378548475233763802883598212) * 10 ^ 70 +
        4936016819969481296469422919065087832221232781892418555732866696889160) * 10 ^ 70 +
        5064206835003023644658317906250506766074737215640021172466947419160038) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (434 - x)) = _
  rw [show 435 = 92 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 21 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (435 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (435 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_435 :
    recurrence4Scalar1First.coeff 435 =
      ((((1838667124466047090695941576562846309400 * 10 ^ 70 +
        6849572007810265913537358904198826970952305405158272565995646237322839) * 10 ^ 70 +
        4156384551535138022044232947961925916895703931876762706251973907234225) * 10 ^ 70 +
        1818057578540547263941886686464114905083201183951031626814795135524445) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (435 - x)) = _
  rw [show 436 = 93 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 20 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (436 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (436 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_436 :
    recurrence4Scalar1First.coeff 436 =
      -((((519947771998177496945004895553318914260 * 10 ^ 70 +
        6755059989400068307043737449047228333946927028140248479783893532979648) * 10 ^ 70 +
        7096884536554212583949927264341779592216169168597056232451882108945429) * 10 ^ 70 +
        2015099563439173497020477252352069438545882519780908397344856864821453) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (436 - x)) = _
  rw [show 437 = 94 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 19 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (437 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (437 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_437 :
    recurrence4Scalar1First.coeff 437 =
      ((((137550090133627734869002959175432566789 * 10 ^ 70 +
        8023537716112700947547686368304499262532614780368144143925065145055094) * 10 ^ 70 +
        5255837501679393859222516063827898760849067101667266512311580817520319) * 10 ^ 70 +
        9372778592864230498662791965267886006153465017022397350294788783016413) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (437 - x)) = _
  rw [show 438 = 95 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 18 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (438 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (438 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_438 :
    recurrence4Scalar1First.coeff 438 =
      -((((34258190887883350613021260536794824722 * 10 ^ 70 +
        3731380313141190541705221460344859316143119970120476576656860977004972) * 10 ^ 70 +
        0292328205059053113790934099740766776500914283622918727951248276633380) * 10 ^ 70 +
        7008012698620379417412516282955613738051776300125431781046675628241615) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (438 - x)) = _
  rw [show 439 = 96 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 17 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (439 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (439 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_439 :
    recurrence4Scalar1First.coeff 439 =
      ((((8059653882482493269792676500371873941 * 10 ^ 70 +
        5735393971065650244648864355057997742673961014084517723826259301882605) * 10 ^ 70 +
        9669086491596466107724014232100552141500418826661669637200209816502390) * 10 ^ 70 +
        4921481547780445788896011593566658209425011535640336109649453164044206) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (439 - x)) = _
  rw [show 440 = 97 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 16 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (440 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (440 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_440 :
    recurrence4Scalar1First.coeff 440 =
      -((((1793699742153961739114921259169943234 * 10 ^ 70 +
        9621651578221724156915102237849737814559710350173701385716891670386566) * 10 ^ 70 +
        4953799958376145485404583866579161864580302892515346595469286877333795) * 10 ^ 70 +
        2454410791100421295075126546854797670051110494049281680652148235265068) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (440 - x)) = _
  rw [show 441 = 98 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 15 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (441 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (441 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_441 :
    recurrence4Scalar1First.coeff 441 =
      ((((377678288997287679420330461715509304 * 10 ^ 70 +
        2258725665208866422734917274115325107596553287458431375106480429565812) * 10 ^ 70 +
        8589482691268026733175312874695732025503523426906873451493136271099831) * 10 ^ 70 +
        3964726710560658367060184656956115518999339964390688607071502970797733) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (441 - x)) = _
  rw [show 442 = 99 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 14 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (442 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (442 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_442 :
    recurrence4Scalar1First.coeff 442 =
      -((((75165130610748354614050578492930413 * 10 ^ 70 +
        7468863276869392054464494939098518050115632751048582140206218679855960) * 10 ^ 70 +
        2044899093177790250580898031616003223669179512296016719545095646982143) * 10 ^ 70 +
        8115402450399405051802669052701326535944328877118030481240821923935908) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (442 - x)) = _
  rw [show 443 = 100 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 13 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (443 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (443 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_443 :
    recurrence4Scalar1First.coeff 443 =
      ((((14110756575262146383967104504207522 * 10 ^ 70 +
        9182092154853989832166622089591597852897162847018124249966178019685113) * 10 ^ 70 +
        6726505183861296457944344713623494727726812045936748464771577699780194) * 10 ^ 70 +
        0498945250661880267536930121081697982749521384907995904585890367903043) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (443 - x)) = _
  rw [show 444 = 101 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 12 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (444 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (444 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_444 :
    recurrence4Scalar1First.coeff 444 =
      -((((2490535228373894451473151415301186 * 10 ^ 70 +
        9832976848242019754806594400430174174043482247921644064373354145097559) * 10 ^ 70 +
        5524700714104365119901839784872153803195423209036313869106811526386144) * 10 ^ 70 +
        5006716165865155423792380079822420828657551101887715468818775947081913) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (444 - x)) = _
  rw [show 445 = 102 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 11 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (445 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (445 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_445 :
    recurrence4Scalar1First.coeff 445 =
      ((((411198317052906556212282426570643 * 10 ^ 70 +
        7429121807804527738890586866961003919114803187518517796581434729629480) * 10 ^ 70 +
        8428130265368596334638881540044352129047048950088125361052516749199978) * 10 ^ 70 +
        5257514650117000049368516044417925143324080127226360506270986321201783) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (445 - x)) = _
  rw [show 446 = 103 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 10 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (446 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (446 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_446 :
    recurrence4Scalar1First.coeff 446 =
      -((((63010807816380085467785160948173 * 10 ^ 70 +
        8346566604341659423264652616204669260711309325025299339708439064626389) * 10 ^ 70 +
        7829606116454419800399942402466795379869488150119129104116152518678778) * 10 ^ 70 +
        6779514188521136476196279631228777379872619203391349350026694381673120) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (446 - x)) = _
  rw [show 447 = 104 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 9 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (447 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (447 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_447 :
    recurrence4Scalar1First.coeff 447 =
      ((((8845898042985131174122301520961 * 10 ^ 70 +
        7352681376980528377081956191745718275390201877414277224681154825607518) * 10 ^ 70 +
        1053403971533867608498104876231365460951011110423966543547865415033541) * 10 ^ 70 +
        9383542884321815016366704887293827810542236180629900509674377877862742) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (447 - x)) = _
  rw [show 448 = 105 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 8 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (448 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (448 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_448 :
    recurrence4Scalar1First.coeff 448 =
      -((((1110813346804849828635270578940 * 10 ^ 70 +
        0999960965851095085863534245219950492681243278116277796857061110823279) * 10 ^ 70 +
        5327004139371033698463203389841231749873352251407899390408033608005328) * 10 ^ 70 +
        5653603565464617944164955180183811323252794436600297981747623663074988) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (448 - x)) = _
  rw [show 449 = 106 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 7 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (449 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (449 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_449 :
    recurrence4Scalar1First.coeff 449 =
      ((((118361280503171025385375604816 * 10 ^ 70 +
        7648562204128493167309815016779586856844353846782662114830936479596197) * 10 ^ 70 +
        0808149765772987677333033238772471273744304764945056669114181919624755) * 10 ^ 70 +
        6475975659517822688255182587250751614567041362158813991192496639701774) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (449 - x)) = _
  rw [show 450 = 107 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 6 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (450 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (450 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_450 :
    recurrence4Scalar1First.coeff 450 =
      -((((9077364107397170311269438631 * 10 ^ 70 +
        5287761500032899647522620918751802329730116681949523420246964499260493) * 10 ^ 70 +
        1276114116201814640950244461214777000134362381159291233532409294053765) * 10 ^ 70 +
        7003332878707380157936625672683017542799468822785219472156520636609047) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (450 - x)) = _
  rw [show 451 = 108 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 5 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (451 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (451 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_451 :
    recurrence4Scalar1First.coeff 451 =
      ((((32345533239381875733341473 * 10 ^ 70 +
        3593842826831284139935886601538486505532082262055986297897236260699634) * 10 ^ 70 +
        4011552165436020067471717060073878156981127726270955925993427795440085) * 10 ^ 70 +
        8587938506439572067687663532961525053426533221190524081142454111554505) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (451 - x)) = _
  rw [show 452 = 109 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 4 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (452 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (452 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_452 :
    recurrence4Scalar1First.coeff 452 =
      ((((169892497040209615602389791 * 10 ^ 70 +
        5700053304604871507140982782120340900805749758527349748479812320245782) * 10 ^ 70 +
        2934162754209129744908672933684977517720943088796807370570866820023709) * 10 ^ 70 +
        9093885348754681307546116217785171734186937179528895753378262031507363) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (452 - x)) = _
  rw [show 453 = 110 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 3 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (453 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (453 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_453 :
    recurrence4Scalar1First.coeff 453 =
      -((((44582824024888724988193003 * 10 ^ 70 +
        6573431810205184517255811470446057897796028211708055057900876971493106) * 10 ^ 70 +
        1209879200265502710891165522715314314869780368140787190105434332959285) * 10 ^ 70 +
        9794452734018647503160586028906583498324903181810174400101086100083369) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (453 - x)) = _
  rw [show 454 = 111 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 2 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (454 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (454 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_454 :
    recurrence4Scalar1First.coeff 454 =
      ((((8216352690576196098078314 * 10 ^ 70 +
        3739508465659787095171807245915174147478287326440556227620919312986111) * 10 ^ 70 +
        9439656085998825430956136861355987010980838842583126690952004971579429) * 10 ^ 70 +
        3395102765978482598584401205038436910780199445590730129465701180173640) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (454 - x)) = _
  rw [show 455 = 112 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 1 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (455 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (455 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_455 :
    recurrence4Scalar1First.coeff 455 =
      -((((1262955106410545500244046 * 10 ^ 70 +
        7000560149105951733246627484125456216997915419656872885960262376513735) * 10 ^ 70 +
        8623214405862055589529036577354042048433997814056812128098322802987106) * 10 ^ 70 +
        9797731391850717503462774483339629643466451895844556561136347467060889) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (455 - x)) = _
  rw [show 456 = 113 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (456 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (456 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_456 :
    recurrence4Scalar1First.coeff 456 =
      ((((169837592462384357129521 * 10 ^ 70 +
        9928040503072880379737156178168666667869220656996793743434828673434549) * 10 ^ 70 +
        5557437988403287392986074310466832528930113735483182269572136334779984) * 10 ^ 70 +
        7301829222815163114814642142242850007018521573179077892600507053466336) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (456 - x)) = _
  rw [show 457 = 114 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 31 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (457 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (457 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_457 :
    recurrence4Scalar1First.coeff 457 =
      -((((20253759511098026991633 * 10 ^ 70 +
        0093910710392227886271602204915354187621171340254029546816023900012342) * 10 ^ 70 +
        4602118431872242948312503057043951993939322797871612723446615740594724) * 10 ^ 70 +
        8381499285640681833586793496668998784593236002084897793286046395364008) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (457 - x)) = _
  rw [show 458 = 115 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 30 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (458 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (458 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_458 :
    recurrence4Scalar1First.coeff 458 =
      ((((2132243542734384572814 * 10 ^ 70 +
        0095559632074990518822021520760100107656389306835890825676817771918807) * 10 ^ 70 +
        8174746001840482059443722019331164335817674764591717684518017930741739) * 10 ^ 70 +
        4801224622222818968507843706865513630423555757543089259121069931705520) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (458 - x)) = _
  rw [show 459 = 116 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 29 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (459 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (459 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_459 :
    recurrence4Scalar1First.coeff 459 =
      -((((193522502780396037866 * 10 ^ 70 +
        1963715796112810753555359291974712810519623426833577793750181092421880) * 10 ^ 70 +
        7905502577504597271055172033922843240851940032542931171139119714446330) * 10 ^ 70 +
        0368200383517942887371042525223594009025564874467095489593637848589127) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (459 - x)) = _
  rw [show 460 = 117 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 28 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (460 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (460 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_460 :
    recurrence4Scalar1First.coeff 460 =
      ((((14212419137419108337 * 10 ^ 70 +
        9695700871707336731290203518699416363873888599934300625834890474017962) * 10 ^ 70 +
        0250101524949246312656394937335979202526947214319236174334509684110670) * 10 ^ 70 +
        7445113409975841187035929279529599670174795101157541820512141336719039) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (460 - x)) = _
  rw [show 461 = 118 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 27 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (461 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (461 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_461 :
    recurrence4Scalar1First.coeff 461 =
      -((((676851404585270119 * 10 ^ 70 +
        7840443534112595912269742626490249071864645151438706750184057188923552) * 10 ^ 70 +
        2192974062282935765059264487791625552457157242326650935854483735544035) * 10 ^ 70 +
        0925773428999474152130708287761097111176290935351311752893888589148976) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (461 - x)) = _
  rw [show 462 = 119 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 26 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (462 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (462 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_462 :
    recurrence4Scalar1First.coeff 462 =
      -((((11912040866373518 * 10 ^ 70 +
        0695352168599085227965797261491894755624677492542027686653972034912328) * 10 ^ 70 +
        9446472865477051714090608585872272304439870044352299236326944497148293) * 10 ^ 70 +
        9178772112991399311729588881281782253592531646044645164898588953389378) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (462 - x)) = _
  rw [show 463 = 120 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 25 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (463 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (463 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_463 :
    recurrence4Scalar1First.coeff 463 =
      ((((7505752630179668 * 10 ^ 70 +
        8132923136409812380882432574573295361438933779543328876523281816454607) * 10 ^ 70 +
        9569582394248842448515257527192357889041007241421626190820710753431079) * 10 ^ 70 +
        7485387521832000940994843110926755230304518594716887125798117949453049) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (463 - x)) = _
  rw [show 464 = 121 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 24 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (464 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (464 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_464 :
    recurrence4Scalar1First.coeff 464 =
      -((((1051587746530481 * 10 ^ 70 +
        6642066116914551698014747445332981779492648726749514317719731183257097) * 10 ^ 70 +
        3655215641534133734180451301289596355979498733962383966800480618642122) * 10 ^ 70 +
        6963898127108625395943715702804955690273740678011760279952724870041738) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (464 - x)) = _
  rw [show 465 = 122 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 23 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (465 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (465 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_465 :
    recurrence4Scalar1First.coeff 465 =
      ((((98324696441297 * 10 ^ 70 +
        5770371919002193806019455730853916213216307840003468961347465573413406) * 10 ^ 70 +
        0371803054296277553906049431805952053817989785441755407462628640307215) * 10 ^ 70 +
        9097662953945287228608143892445236766989545275054061676801122829918671) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (465 - x)) = _
  rw [show 466 = 123 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 22 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (466 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (466 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_466 :
    recurrence4Scalar1First.coeff 466 =
      -((((6512942407355 * 10 ^ 70 +
        2769845278009641941232057209533571348808156165142776413910496817455634) * 10 ^ 70 +
        7838036202333294830511908875073989864384625028205504939629908128273718) * 10 ^ 70 +
        9761718271454401282496561727312513151148348881319686504169133680784012) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (466 - x)) = _
  rw [show 467 = 124 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 21 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (467 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (467 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_467 :
    recurrence4Scalar1First.coeff 467 =
      ((((246685725995 * 10 ^ 70 +
        9782294656210889165779012059850003265819588907425359035645920064772678) * 10 ^ 70 +
        0729702618218854052250181233222761894194959877402674978663365328511930) * 10 ^ 70 +
        0430911623565056349484579205664371419539754598065375536565490225746678) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (467 - x)) = _
  rw [show 468 = 125 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 20 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (468 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (468 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_468 :
    recurrence4Scalar1First.coeff 468 =
      ((((5721656605 * 10 ^ 70 +
        1100155284601409499295615931399544311460460210746880980393329911921158) * 10 ^ 70 +
        6086464204440646651378579191280326696949057013710873943671586053413939) * 10 ^ 70 +
        5317869981542624221102032235780859927037027740311007536680075519812673) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (468 - x)) = _
  rw [show 469 = 126 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 19 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (469 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (469 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_469 :
    recurrence4Scalar1First.coeff 469 =
      -((((1848757159 * 10 ^ 70 +
        8581478102623126944909126193400723001732519797788866487834664465865696) * 10 ^ 70 +
        1904948119900124714321145304629001300152725140923198171454918619705622) * 10 ^ 70 +
        2598203703898251469298661628860835129705606298401355850743010667468023) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (469 - x)) = _
  rw [show 470 = 127 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 18 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (470 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (470 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_470 :
    recurrence4Scalar1First.coeff 470 =
      ((((168001804 * 10 ^ 70 +
        1115948583582087980595709174820757600512644434220881750702070613507374) * 10 ^ 70 +
        5042122668749876483382556554538485167508046169894864941091651824245941) * 10 ^ 70 +
        2684307540427718912150874669594667957143295177215770483844037044602444) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (470 - x)) = _
  rw [show 471 = 128 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 17 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (471 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (471 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_471 :
    recurrence4Scalar1First.coeff 471 =
      -((((9118060 * 10 ^ 70 +
        9342227595684593400402307317227234097963136100007298318148974102959610) * 10 ^ 70 +
        8774388019672774075945321629722650088872011382725834601900199882447846) * 10 ^ 70 +
        8390517262836699892005986349292548573434817421129071603324631042358093) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (471 - x)) = _
  rw [show 472 = 129 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 16 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (472 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (472 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_472 :
    recurrence4Scalar1First.coeff 472 =
      ((((250753 * 10 ^ 70 +
        3576167343717293255590845073319369596156696085549696888168128784491337) * 10 ^ 70 +
        6337801992601095663716661377454802666038498678003979181044719398897719) * 10 ^ 70 +
        8706596396931308320165707700733997131308538346579616356342163970518770) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (472 - x)) = _
  rw [show 473 = 130 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 15 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (473 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (473 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_473 :
    recurrence4Scalar1First.coeff 473 =
      ((((5152 * 10 ^ 70 +
        4629215070575844341531869567195676171973212241552904231924124027982109) * 10 ^ 70 +
        2339402797066435354588860758594073530111982849485952465932757236775767) * 10 ^ 70 +
        0832754560011436992777257759801617948668106693509484388723057853630059) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (473 - x)) = _
  rw [show 474 = 131 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 14 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (474 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (474 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_474 :
    recurrence4Scalar1First.coeff 474 =
      -((((907 * 10 ^ 70 +
        3892103941242784660790793792271454217500950504734630219468083392677393) * 10 ^ 70 +
        3315513429774162729326007481856705598593856723148427702755844833398861) * 10 ^ 70 +
        2459705604167789154231421864408515891330735756957614555435043397585154) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (474 - x)) = _
  rw [show 475 = 132 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 13 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (475 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (475 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_475 :
    recurrence4Scalar1First.coeff 475 =
      ((((43 * 10 ^ 70 +
        9145457361110369285285598407383734029994604838224810212468064338038981) * 10 ^ 70 +
        9757626508640410888086343859175714653552671280097915540537851705674661) * 10 ^ 70 +
        7384817694761147712406002580360888523503755413483773801856644726452059) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (475 - x)) = _
  rw [show 476 = 133 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 12 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (476 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (476 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_476 :
    recurrence4Scalar1First.coeff 476 =
      -(((8630150453406617890951592861916501457947717440448650460528922550882542 * 10 ^ 70 +
        4818917122128416410541703990802810224215818093644452260194961421212525) * 10 ^ 70 +
        3892966053240573167678430150598276320841003350740399618414402793669086) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (476 - x)) = _
  rw [show 477 = 134 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 11 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (477 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (477 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_477 :
    recurrence4Scalar1First.coeff 477 =
      -(((150046024558216634430908223171364108976208871546421372433022246795929 * 10 ^ 70 +
        3235358425524859425965787435739776007346029812987850108680276000372997) * 10 ^ 70 +
        8036593994838664854735553309337479395329438156661659870107929629737132) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (477 - x)) = _
  rw [show 478 = 135 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 10 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (478 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (478 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_478 :
    recurrence4Scalar1First.coeff 478 =
      (((12573588951064079787261767941931747931658333277899406928643917323541 * 10 ^ 70 +
        1711822745272751899518154444096001592574536568529803826789308779129857) * 10 ^ 70 +
        5034496875789545957806497511695292989450888670229914849290090247092241) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (478 - x)) = _
  rw [show 479 = 136 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 9 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (479 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (479 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_479 :
    recurrence4Scalar1First.coeff 479 =
      -(((209589070113555646023053802508960172284259072441423819082912659269 * 10 ^ 70 +
        9808951919185102112870310364838558005402348112008968990126419937727174) * 10 ^ 70 +
        9552805656224898631890912288081250600410556679478307038671096207174594) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (479 - x)) = _
  rw [show 480 = 137 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 8 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_479_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (480 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (480 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_480 :
    recurrence4Scalar1First.coeff 480 =
      -(((2735167132955559180408905565668959476472212069394223692449034301 * 10 ^ 70 +
        6991259780557913546576044309586145317880981014654882940479947575728439) * 10 ^ 70 +
        8327233164145774560302455203684255160387230409025223626929362358899040) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (480 - x)) = _
  rw [show 481 = 138 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 7 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_480_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (481 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (481 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_481 :
    recurrence4Scalar1First.coeff 481 =
      (((109465818727350610099543711145551895500393979789267722581891644 * 10 ^ 70 +
        5567175835700291509826763743557244764571971732268835121470229368364840) * 10 ^ 70 +
        7697838799469164700188159985333149206519416123383211906715312019038224) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (481 - x)) = _
  rw [show 482 = 139 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 6 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_481_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (482 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (482 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_482 :
    recurrence4Scalar1First.coeff 482 =
      (((114098085597399545196246396470584643239447369472257458145459 * 10 ^ 70 +
        5032325164817294609210907539104204401283829184808244114883447129685129) * 10 ^ 70 +
        9878117894627160450143866359795819025252487488571510836420120211088852) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (482 - x)) = _
  rw [show 483 = 140 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 5 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_482_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (483 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (483 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_483 :
    recurrence4Scalar1First.coeff 483 =
      -(((21079716471050467252194432305119714207422246558881626358805 * 10 ^ 70 +
        6221531323816400268390130777239976220840111283647786156954682939299440) * 10 ^ 70 +
        5437369894713045825081640917492565368317420251974367493945378033181106) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (483 - x)) = _
  rw [show 484 = 141 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 4 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_483_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (484 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (484 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_484 :
    recurrence4Scalar1First.coeff 484 =
      -(((21877908131638057693534703529642911212818323599467611714 * 10 ^ 70 +
        6372418314912375880260698354550874261220095088798311022138481575565020) * 10 ^ 70 +
        1899597889143954578408806716242437783853556039842641760513144445299563) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (484 - x)) = _
  rw [show 485 = 142 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 3 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_484_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (485 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (485 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_485 :
    recurrence4Scalar1First.coeff 485 =
      (((1972339663927866737605700270737996706289734166773571040 * 10 ^ 70 +
        7441237727456753488584435153992849406395933449089465995541091694425369) * 10 ^ 70 +
        8191272826085369452760292328545116035530504668279621566579650235412799) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (485 - x)) = _
  rw [show 486 = 143 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 2 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_485_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (486 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (486 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_486 :
    recurrence4Scalar1First.coeff 486 =
      (((6116730521157699241962726464081025395313241970716344 * 10 ^ 70 +
        1380963709523931386407910904855836950945172172175496761804897806021562) * 10 ^ 70 +
        1039838676398830753397615803318320605232601997062904127441000195653097) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (486 - x)) = _
  rw [show 487 = 144 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 1 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_486_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (487 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (487 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_487 :
    recurrence4Scalar1First.coeff 487 =
      -(((74648090932077347353263753864833245709248293104249 * 10 ^ 70 +
        6576722286580108023576817125411503525848590422123583849366601609915960) * 10 ^ 70 +
        8384450081969754806502709479764596001436371663463968914365435306373618) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (487 - x)) = _
  rw [show 488 = 145 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_487_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (488 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (488 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_488 :
    recurrence4Scalar1First.coeff 488 =
      -(((339186021775847190861139694017958971968887438604 * 10 ^ 70 +
        6139956025663920525971554393110091145678015254756696528326141524395508) * 10 ^ 70 +
        1015276928984203431723370644458172977932351107427333238642909499029449) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (488 - x)) = _
  rw [show 489 = 146 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 31 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_488_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (489 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (489 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_489 :
    recurrence4Scalar1First.coeff 489 =
      (((1232530091055216136077249860747126090406097399 * 10 ^ 70 +
        3059518758004075414674490120195176815526103905813540399414028159374438) * 10 ^ 70 +
        8343796897954486759119787895257680868756527970904822041451633848520742) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (489 - x)) = _
  rw [show 490 = 147 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 30 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_489_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (490 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 314,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (490 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_490 :
    recurrence4Scalar1First.coeff 490 =
      (((7526124239358483796856268347382848283365740 * 10 ^ 70 +
        8054345538169604571634557221321238005660153360147357220966666696118537) * 10 ^ 70 +
        7126156916716859073453133213501095328376111803953648037514277455286518) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (490 - x)) = _
  rw [show 491 = 148 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 29 +
      314 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_490_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (491 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 315,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (491 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_491 :
    recurrence4Scalar1First.coeff 491 =
      -(((9312190052053424212586533715395067321455 * 10 ^ 70 +
        7995809174577019192275481238950303169296101861530076184249339365101968) * 10 ^ 70 +
        7793388981916622203304667223701557712195187170546309034223255199648127) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (491 - x)) = _
  rw [show 492 = 149 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 28 +
      315 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_491_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (492 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 316,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (492 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_492 :
    recurrence4Scalar1First.coeff 492 =
      -(((81536586444739608178053319965601833224 * 10 ^ 70 +
        3363586451380916348146503841139944016616395126512275041466259170764934) * 10 ^ 70 +
        1828485571491685981343824807054481375254622381431793403942827219627406) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (492 - x)) = _
  rw [show 493 = 150 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 27 +
      316 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_492_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (493 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 317,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (493 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_493 :
    recurrence4Scalar1First.coeff 493 =
      (((42467609532802624975544424386539137 * 10 ^ 70 +
        6101704001284299665339319760306209932844299739375997660039582470903992) * 10 ^ 70 +
        3438253238152746194610539939453653348668719302981521561659335562193818) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (493 - x)) = _
  rw [show 494 = 151 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 26 +
      317 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_493_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (494 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 318,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (494 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_494 :
    recurrence4Scalar1First.coeff 494 =
      (((490810692449436746794488338981596 * 10 ^ 70 +
        2492477523389816807277515003689744430725304468636020534881247752764615) * 10 ^ 70 +
        2322174316644426123543975176112026210624582287561861273962149196770062) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (494 - x)) = _
  rw [show 495 = 152 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 25 +
      318 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_494_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (495 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 319,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (495 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_495 :
    recurrence4Scalar1First.coeff 495 =
      -(((210097027913814188838807220613 * 10 ^ 70 +
        0840473736124601249973586663604480651128551179649532635407127042023259) * 10 ^ 70 +
        9739748607811914372380651790389901051880282629597113635641916003459856) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (495 - x)) = _
  rw [show 496 = 153 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 24 +
      319 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_495_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (496 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 320,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (496 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_496 :
    recurrence4Scalar1First.coeff 496 =
      -(((1642172443042872222668543852 * 10 ^ 70 +
        9037417640025370136667214888040987054407916365344370239264547941478712) * 10 ^ 70 +
        5928044549193440995381480775627326645990648327491370346907184824326443) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (496 - x)) = _
  rw [show 497 = 154 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 23 +
      320 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_496_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (497 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 321,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (497 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_497 :
    recurrence4Scalar1First.coeff 497 =
      (((1008497370059499659711662 * 10 ^ 70 +
        3676708471849466564292967881348637453070266263160376135612080697500600) * 10 ^ 70 +
        2658840564901637275524884732067381204845850078614750164734704123594228) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (497 - x)) = _
  rw [show 498 = 155 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 22 +
      321 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_497_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (498 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 322,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (498 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_498 :
    recurrence4Scalar1First.coeff 498 =
      (((2544942759587124200259 * 10 ^ 70 +
        2346188935835411478316915752449305401831361591637033140320656322287736) * 10 ^ 70 +
        9841788622251137119611954794919155212095118397128158994391423535073337) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (498 - x)) = _
  rw [show 499 = 156 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 21 +
      322 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_498_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (499 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 323,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (499 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_499 :
    recurrence4Scalar1First.coeff 499 =
      -(((2226143944909891390 * 10 ^ 70 +
        9835121376077371204266789095475373946368531243131046493017575471397725) * 10 ^ 70 +
        5156155595573248780810428045991922936496191733714313063662357838195479) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (499 - x)) = _
  rw [show 500 = 157 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 20 +
      323 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_499_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (500 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 324,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (500 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_500 :
    recurrence4Scalar1First.coeff 500 =
      -(((945097891307393 * 10 ^ 70 +
        4682845961491778028504175512787514419124240180440771506096860628266110) * 10 ^ 70 +
        1492392031003527309671190307246878191022875214254828547286751702904123) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (500 - x)) = _
  rw [show 501 = 158 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 19 +
      324 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_500_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (501 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 325,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (501 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_501 :
    recurrence4Scalar1First.coeff 501 =
      (((1180937056767 * 10 ^ 70 +
        1673237875357378323544708086603741009779417305850960408830990918322263) * 10 ^ 70 +
        8832923049849030556904813858899408362808586811767339575576884580072377) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (501 - x)) = _
  rw [show 502 = 159 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 18 +
      325 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_501_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (502 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 326,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (502 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_502 :
    recurrence4Scalar1First.coeff 502 =
      -(((115282679 * 10 ^ 70 +
        3132037069055099157111363858862768609496498545148931800517812141412679) * 10 ^ 70 +
        0212708086825054015190823615790272034400361985005940435701368659363382) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (502 - x)) = _
  rw [show 503 = 160 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 17 +
      326 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_502_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (503 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 327,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (503 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_503 :
    recurrence4Scalar1First.coeff 503 =
      -(((95784 * 10 ^ 70 +
        7051279528726760760701577470682221342369726174083271247623349401785487) * 10 ^ 70 +
        2373935467374019213757725834598087182271605729535360340421467025169037) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (503 - x)) = _
  rw [show 504 = 161 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 16 +
      327 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_503_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (504 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 328,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (504 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_504 :
    recurrence4Scalar1First.coeff 504 =
      (((17 * 10 ^ 70 +
        1432416920070436566929847924499860641182379648291476220965161296186630) * 10 ^ 70 +
        0494804242371929568006463141020811377612354686409038889734322041482735) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (504 - x)) = _
  rw [show 505 = 162 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 15 +
      328 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_504_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (505 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 329,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (505 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_505 :
    recurrence4Scalar1First.coeff 505 =
      ((3210542217947617211629707595273107072249483294653354853480542839735 * 10 ^ 70 +
        9469660170781244095820924612961028802431063684617787521823127394230495) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (505 - x)) = _
  rw [show 506 = 163 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 14 +
      329 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_505_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (506 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 330,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (506 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_506 :
    recurrence4Scalar1First.coeff 506 =
      -((1590329813036954421921444186742491627397130701811589226779313682 * 10 ^ 70 +
        5923245748844080217507673083911685369154251669696572418678451075909769) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (506 - x)) = _
  rw [show 507 = 164 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 13 +
      330 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_506_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (507 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 331,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (507 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_507 :
    recurrence4Scalar1First.coeff 507 =
      ((44917810696009707609319006854678105930269483758512676000761 * 10 ^ 70 +
        7357273229078575866667622182882415175585991549867038059019172437909960) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (507 - x)) = _
  rw [show 508 = 165 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 12 +
      331 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_507_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (508 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 332,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (508 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_508 :
    recurrence4Scalar1First.coeff 508 =
      ((780703593417263659911223146443448232981528409591408128 * 10 ^ 70 +
        9857614745312238910434906780923508811921870089215904497962479278599674) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (508 - x)) = _
  rw [show 509 = 166 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 11 +
      332 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_508_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (509 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 333,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (509 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_509 :
    recurrence4Scalar1First.coeff 509 =
      -((29150508356483022930565045869325200584398564614598 * 10 ^ 70 +
        0960616034432173973688958591864501792297153353224219935340974091172560) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (509 - x)) = _
  rw [show 510 = 167 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 10 +
      333 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_509_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (510 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 334,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (510 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_510 :
    recurrence4Scalar1First.coeff 510 =
      ((103017743661360131232578851696511847305370894 * 10 ^ 70 +
        6797074169192186865706376482645903159289366802910811244660784014754088) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (510 - x)) = _
  rw [show 511 = 168 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 9 +
      334 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_510_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (511 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 335,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (511 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_511 :
    recurrence4Scalar1First.coeff 511 =
      ((605206929389022692376173192279101523284 * 10 ^ 70 +
        3768782281772964258988716477801130602553785652613462389782044679436313) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (511 - x)) = _
  rw [show 512 = 169 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 8 +
      335 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_511_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (512 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 336,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (512 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_512 :
    recurrence4Scalar1First.coeff 512 =
      -((2387564210795561767331640168739011 * 10 ^ 70 +
        1055656557510652155564391597591862663130937896343765201276236665781971) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (512 - x)) = _
  rw [show 513 = 170 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 7 +
      336 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_512_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (513 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 337,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (513 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_513 :
    recurrence4Scalar1First.coeff 513 =
      ((722923329923565252946204848 * 10 ^ 70 +
        1485352938550773357973813673894293528915621928611917809580688545632809) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (513 - x)) = _
  rw [show 514 = 171 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 6 +
      337 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_513_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (514 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 338,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (514 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_514 :
    recurrence4Scalar1First.coeff 514 =
      ((639227295447097744006 * 10 ^ 70 +
        6949833568875890757490842621048178695602214816757076895539676784710869) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (514 - x)) = _
  rw [show 515 = 172 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 5 +
      338 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_514_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
