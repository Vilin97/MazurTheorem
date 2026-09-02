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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
