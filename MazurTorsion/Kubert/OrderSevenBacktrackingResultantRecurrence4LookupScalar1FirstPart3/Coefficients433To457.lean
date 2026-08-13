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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
