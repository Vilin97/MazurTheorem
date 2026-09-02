/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
