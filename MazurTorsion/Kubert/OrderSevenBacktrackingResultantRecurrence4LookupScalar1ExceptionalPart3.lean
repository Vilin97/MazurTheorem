/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27

attribute [local simp]
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91

attribute [local simp]
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
  recurrence4ExceptionalProduct_coeff_234
  recurrence4ExceptionalProduct_coeff_235
  recurrence4ExceptionalProduct_coeff_236
  recurrence4ExceptionalProduct_coeff_237
  recurrence4ExceptionalProduct_coeff_238
  recurrence4ExceptionalProduct_coeff_239
  recurrence4ExceptionalProduct_coeff_240
  recurrence4ExceptionalProduct_coeff_241
  recurrence4ExceptionalProduct_coeff_242
  recurrence4ExceptionalProduct_coeff_243
  recurrence4ExceptionalProduct_coeff_244
  recurrence4ExceptionalProduct_coeff_245
  recurrence4ExceptionalProduct_coeff_246
  recurrence4ExceptionalProduct_coeff_247
  recurrence4ExceptionalProduct_coeff_248
  recurrence4ExceptionalProduct_coeff_249
  recurrence4ExceptionalProduct_coeff_250
  recurrence4ExceptionalProduct_coeff_251
  recurrence4ExceptionalProduct_coeff_252
  recurrence4ExceptionalProduct_coeff_253
  recurrence4ExceptionalProduct_coeff_254
  recurrence4ExceptionalProduct_coeff_255
  recurrence4ExceptionalProduct_coeff_256
  recurrence4ExceptionalProduct_coeff_257
  recurrence4ExceptionalProduct_coeff_258
  recurrence4ExceptionalProduct_coeff_259
  recurrence4ExceptionalProduct_coeff_260
  recurrence4ExceptionalProduct_coeff_261
  recurrence4ExceptionalProduct_coeff_262
  recurrence4ExceptionalProduct_coeff_263
  recurrence4ExceptionalProduct_coeff_264
  recurrence4ExceptionalProduct_coeff_265
  recurrence4ExceptionalProduct_coeff_266
  recurrence4ExceptionalProduct_coeff_267
  recurrence4ExceptionalProduct_coeff_268
  recurrence4ExceptionalProduct_coeff_269
  recurrence4ExceptionalProduct_coeff_270
  recurrence4ExceptionalProduct_coeff_271
  recurrence4ExceptionalProduct_coeff_272
  recurrence4ExceptionalProduct_coeff_273
  recurrence4ExceptionalProduct_coeff_274
  recurrence4ExceptionalProduct_coeff_275
  recurrence4ExceptionalProduct_coeff_276
  recurrence4ExceptionalProduct_coeff_277
  recurrence4ExceptionalProduct_coeff_278
  recurrence4ExceptionalProduct_coeff_279
  recurrence4ExceptionalProduct_coeff_280
  recurrence4ExceptionalProduct_coeff_281
  recurrence4ExceptionalProduct_coeff_282
  recurrence4ExceptionalProduct_coeff_283
  recurrence4ExceptionalProduct_coeff_284
  recurrence4ExceptionalProduct_coeff_285
  recurrence4ExceptionalProduct_coeff_286
  recurrence4ExceptionalProduct_coeff_287
  recurrence4ExceptionalProduct_coeff_288
  recurrence4ExceptionalProduct_coeff_289

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_290
  recurrence4ExceptionalProduct_coeff_291
  recurrence4ExceptionalProduct_coeff_292
  recurrence4ExceptionalProduct_coeff_293
  recurrence4ExceptionalProduct_coeff_294
  recurrence4ExceptionalProduct_coeff_295
  recurrence4ExceptionalProduct_coeff_296
  recurrence4ExceptionalProduct_coeff_297
  recurrence4ExceptionalProduct_coeff_298
  recurrence4ExceptionalProduct_coeff_299
  recurrence4ExceptionalProduct_coeff_300
  recurrence4ExceptionalProduct_coeff_301
  recurrence4ExceptionalProduct_coeff_302
  recurrence4ExceptionalProduct_coeff_303
  recurrence4ExceptionalProduct_coeff_304
  recurrence4ExceptionalProduct_coeff_305
  recurrence4ExceptionalProduct_coeff_306
  recurrence4ExceptionalProduct_coeff_307
  recurrence4ExceptionalProduct_coeff_308
  recurrence4ExceptionalProduct_coeff_309
  recurrence4ExceptionalProduct_coeff_310
  recurrence4ExceptionalProduct_coeff_311
  recurrence4ExceptionalProduct_coeff_312
  recurrence4ExceptionalProduct_coeff_313
  recurrence4ExceptionalProduct_coeff_314
  recurrence4ExceptionalProduct_coeff_315
  recurrence4ExceptionalProduct_coeff_316
  recurrence4ExceptionalProduct_coeff_317
  recurrence4ExceptionalProduct_coeff_318
  recurrence4ExceptionalProduct_coeff_319
  recurrence4ExceptionalProduct_coeff_320
  recurrence4ExceptionalProduct_coeff_321
  recurrence4ExceptionalProduct_coeff_322
  recurrence4ExceptionalProduct_coeff_323
  recurrence4ExceptionalProduct_coeff_324
  recurrence4ExceptionalProduct_coeff_325
  recurrence4ExceptionalProduct_coeff_326
  recurrence4ExceptionalProduct_coeff_327
  recurrence4ExceptionalProduct_coeff_328
  recurrence4ExceptionalProduct_coeff_329
  recurrence4ExceptionalProduct_coeff_330
  recurrence4ExceptionalProduct_coeff_331
  recurrence4ExceptionalProduct_coeff_332
  recurrence4ExceptionalProduct_coeff_333
  recurrence4ExceptionalProduct_coeff_334
  recurrence4ExceptionalProduct_coeff_335
  recurrence4ExceptionalProduct_coeff_336
  recurrence4ExceptionalProduct_coeff_337
  recurrence4ExceptionalProduct_coeff_338
  recurrence4ExceptionalProduct_coeff_339
  recurrence4ExceptionalProduct_coeff_340
  recurrence4ExceptionalProduct_coeff_341
  recurrence4ExceptionalProduct_coeff_342
  recurrence4ExceptionalProduct_coeff_343
  recurrence4ExceptionalProduct_coeff_344
  recurrence4ExceptionalProduct_coeff_345
  recurrence4ExceptionalProduct_coeff_346
  recurrence4ExceptionalProduct_coeff_347
  recurrence4ExceptionalProduct_coeff_348
  recurrence4ExceptionalProduct_coeff_349
  recurrence4ExceptionalProduct_coeff_350
  recurrence4ExceptionalProduct_coeff_351
  recurrence4ExceptionalProduct_coeff_352
  recurrence4ExceptionalProduct_coeff_353

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_354
  recurrence4ExceptionalProduct_coeff_355
  recurrence4ExceptionalProduct_coeff_356
  recurrence4ExceptionalProduct_coeff_357
  recurrence4ExceptionalProduct_coeff_358
  recurrence4ExceptionalProduct_coeff_359
  recurrence4ExceptionalProduct_coeff_360
  recurrence4ExceptionalProduct_coeff_361
  recurrence4ExceptionalProduct_coeff_362
  recurrence4ExceptionalProduct_coeff_363
  recurrence4ExceptionalProduct_coeff_364
  recurrence4ExceptionalProduct_coeff_365
  recurrence4ExceptionalProduct_coeff_366
  recurrence4ExceptionalProduct_coeff_367
  recurrence4ExceptionalProduct_coeff_368
  recurrence4ExceptionalProduct_coeff_369

private theorem recurrence4Scalar1Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (383 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (383 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_383 :
    recurrence4Scalar1Exceptional.coeff 383 =
      -((((18052272435675936204309057999031231258897316922678019159648781520 * 10 ^ 70 +
        2209915408470326076269551367618167881741520952074775774439704372187666) * 10 ^ 70 +
        5874407883950220709808609088715669753684696440527106508481559207747014) * 10 ^ 70 +
        9624530974765399855583789362449401428064777619677505739387077760605567) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (383 - x)) = _
  rw [show 384 = 234 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 8 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (384 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (384 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_384 :
    recurrence4Scalar1Exceptional.coeff 384 =
      ((((4224866243334306523135427007298476760720900432518714795590796330 * 10 ^ 70 +
        1182054810369761201013308128214226390146808427618224526752042009576820) * 10 ^ 70 +
        3916396197218658337275046738871373904459097778449468168724117601713051) * 10 ^ 70 +
        0313237541368117701399155724025943211661636755351003314623055508996714) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (384 - x)) = _
  rw [show 385 = 235 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 7 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (385 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (385 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_385 :
    recurrence4Scalar1Exceptional.coeff 385 =
      -((((662874295420186577683928642718118272731828662733491075917491188 * 10 ^ 70 +
        0059757006765952423455901313578635299021925109726067921620503995460011) * 10 ^ 70 +
        4363787080733505701327012469526814313266419916479346755246000009134595) * 10 ^ 70 +
        4176416954496709466018839941210842336051775608766995218236228419776585) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (385 - x)) = _
  rw [show 386 = 236 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 6 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (386 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (386 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_386 :
    recurrence4Scalar1Exceptional.coeff 386 =
      -((((61800650155862182105719311869660822433559686682257881943886246 * 10 ^ 70 +
        5773465711003494838579454846656074907763056979153823107879985958693492) * 10 ^ 70 +
        1019068710136845146917056894230754799485913567610556261869521348452130) * 10 ^ 70 +
        1005746647971025068140056024289807978489570965785416515715403775155583) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (386 - x)) = _
  rw [show 387 = 237 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 5 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (387 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (387 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_387 :
    recurrence4Scalar1Exceptional.coeff 387 =
      ((((120818288829698441399129998540397926581259992583710305011496277 * 10 ^ 70 +
        1985003664291952527771503494571728021469608110677688020460673335507843) * 10 ^ 70 +
        4596073970856662097010505986519714610884063599631522526456025438956533) * 10 ^ 70 +
        4279630833821688505055584155397416679079647113868270011482341442214321) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (387 - x)) = _
  rw [show 388 = 238 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 4 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (388 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (388 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_388 :
    recurrence4Scalar1Exceptional.coeff 388 =
      -((((74249969692121822178946750915769117687780874808778624101679941 * 10 ^ 70 +
        8110395430909268630103340707653801933482262792801782123535639632069146) * 10 ^ 70 +
        0425195509608745278272838838725899460282846041734687275240895334852811) * 10 ^ 70 +
        4461446659647160538124036834401965823152108236120986844190257897004344) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (388 - x)) = _
  rw [show 389 = 239 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 3 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (389 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (389 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_389 :
    recurrence4Scalar1Exceptional.coeff 389 =
      ((((36120050517835347782257454690889594211901757846307060384601960 * 10 ^ 70 +
        1920463792836276486236914676195733111714617353807067637737349340869458) * 10 ^ 70 +
        9174332995540809213368092642353287041274252065254748408895884411906027) * 10 ^ 70 +
        0866963860266218171969102372299429224131099737696525223054808158480701) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (389 - x)) = _
  rw [show 390 = 240 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 2 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (390 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (390 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_390 :
    recurrence4Scalar1Exceptional.coeff 390 =
      -((((15950409903695678086309350749367587075341878944748123739263689 * 10 ^ 70 +
        3475033184019640231267909795629433883817878398484061373333631380528313) * 10 ^ 70 +
        8479297987857919046197892547228729119607838949670862796791016882486678) * 10 ^ 70 +
        7674737228517269877511038678728552595934623668995249856812848824642686) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (390 - x)) = _
  rw [show 391 = 241 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 1 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (391 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (391 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_391 :
    recurrence4Scalar1Exceptional.coeff 391 =
      ((((6749068036211538135355156281893148884226522184938340937914293 * 10 ^ 70 +
        5728188117065275114597780679870472125389929722197728425329659081008906) * 10 ^ 70 +
        7155599785832981553566438045708701225348712898678680280882132395320901) * 10 ^ 70 +
        6224617910776668476006338712970095085925584986722921487340776848699823) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (391 - x)) = _
  rw [show 392 = 242 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (392 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (392 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_392 :
    recurrence4Scalar1Exceptional.coeff 392 =
      -((((2812097454699148755030244344210908242622591130220696886861262 * 10 ^ 70 +
        1612670798806859976907144112318380124964379844089854808315837801935731) * 10 ^ 70 +
        1465906036972355535274850926892661569355286550808964872583422279507716) * 10 ^ 70 +
        1253236322711841212308012437641220455729717916334004113498244229794180) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (392 - x)) = _
  rw [show 393 = 243 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 31 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (393 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (393 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_393 :
    recurrence4Scalar1Exceptional.coeff 393 =
      ((((1167508782700760428990236022923987059475103829507433771557614 * 10 ^ 70 +
        2506092633129738979269848601037946097168348491312592337397786845773661) * 10 ^ 70 +
        7954601248695758351476621803835260755438416173354459875522181236785279) * 10 ^ 70 +
        9171927425296381123978548741824246161173725724100629536855980707242527) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (393 - x)) = _
  rw [show 394 = 244 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 30 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (394 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (394 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_394 :
    recurrence4Scalar1Exceptional.coeff 394 =
      -((((483232701264813798914485859767888130717615162013252797601275 * 10 ^ 70 +
        8213598442290321024949351491794927659936195002490855201712660704596099) * 10 ^ 70 +
        4877003871660107837733210418187282239955844509348758020150685392555925) * 10 ^ 70 +
        1706740951502540143340778617940315100297343555658756960360560758465600) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (394 - x)) = _
  rw [show 395 = 245 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 29 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (395 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (395 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_395 :
    recurrence4Scalar1Exceptional.coeff 395 =
      ((((198090029114758334508239851271728799073753482575901476307986 * 10 ^ 70 +
        1019715693022081584456395069918918928860510594416466745091562360069158) * 10 ^ 70 +
        9355388090583531335351290283850976051722807006044568939067686103758277) * 10 ^ 70 +
        5110119842761599537868946176026669224702271514401195508688353171166130) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (395 - x)) = _
  rw [show 396 = 246 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 28 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (396 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (396 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_396 :
    recurrence4Scalar1Exceptional.coeff 396 =
      -((((79670455423483430195956625041008404164217623779414909557455 * 10 ^ 70 +
        3403123524699332612647668189729802088963453623417050980605818809778301) * 10 ^ 70 +
        1697289824363104489225032179812866007651781168177305963548212367024615) * 10 ^ 70 +
        5014280789984756328891191274309603393496204592793404157648221235374141) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (396 - x)) = _
  rw [show 397 = 247 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 27 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (397 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (397 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_397 :
    recurrence4Scalar1Exceptional.coeff 397 =
      ((((31148936114351143779523336349895476260802275958578472945924 * 10 ^ 70 +
        7971144893327991721886142237555725371571769044100307626226632465160393) * 10 ^ 70 +
        9017208476858306702250165013850714260764096297792044377756542105589824) * 10 ^ 70 +
        1312079296819735717140170563125046095172261349539504544118725340416593) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (397 - x)) = _
  rw [show 398 = 248 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 26 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (398 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (398 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_398 :
    recurrence4Scalar1Exceptional.coeff 398 =
      -((((11745851069092318826691147466045146789116248142238925341026 * 10 ^ 70 +
        6794146143778789648590196855715287549516533864567559573195394394194340) * 10 ^ 70 +
        3887522263004406086311485621108978586375213857694885351637110576591191) * 10 ^ 70 +
        8902693689372066308954616926431288836511638821783787813227299560489370) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (398 - x)) = _
  rw [show 399 = 249 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 25 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (399 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (399 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_399 :
    recurrence4Scalar1Exceptional.coeff 399 =
      ((((4244204792928496231223755071523777979818138978616505889207 * 10 ^ 70 +
        7670442362786982438664149306620914925081370237389859627611712436659483) * 10 ^ 70 +
        2984518083026643781722454734074422665965007029739365075022321110031113) * 10 ^ 70 +
        8854067150225596069651180181047615035660207494336728284830634227820641) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (399 - x)) = _
  rw [show 400 = 250 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 24 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (400 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (400 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_400 :
    recurrence4Scalar1Exceptional.coeff 400 =
      -((((1460995379549872475324477146351913532368582916210552387490 * 10 ^ 70 +
        8182378455548834641372145809905660764009272284921862293769625267162101) * 10 ^ 70 +
        0163759469861653985423240209162041987425618446291414939203026611758021) * 10 ^ 70 +
        7491809899251011783729584008672550233623527230439288172727610437960868) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (400 - x)) = _
  rw [show 401 = 251 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 23 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (401 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (401 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_401 :
    recurrence4Scalar1Exceptional.coeff 401 =
      ((((476158767397510520417291522012505596986784077388263652758 * 10 ^ 70 +
        0177108740448042302402580698241252808403348124202158349149198529137353) * 10 ^ 70 +
        1922988590241405690323955414478244566913385387840573870750639769071035) * 10 ^ 70 +
        2290878029136809663406173444098707349875534803145699148772762617275455) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (401 - x)) = _
  rw [show 402 = 252 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 22 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (402 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (402 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_402 :
    recurrence4Scalar1Exceptional.coeff 402 =
      -((((145743465415009079367871029961368591399887008269734445501 * 10 ^ 70 +
        2405507238632435742689008141954365977728185958878670066761274037711984) * 10 ^ 70 +
        2624182019829749102273156148485707366231983872720499205449207442024031) * 10 ^ 70 +
        5436120589563663061317867677099845546830349144244814746548083356994008) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (402 - x)) = _
  rw [show 403 = 253 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 21 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (403 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (403 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_403 :
    recurrence4Scalar1Exceptional.coeff 403 =
      ((((41364510424055712668552156912283877525975803253779221195 * 10 ^ 70 +
        7145953159406364356980113032208464030308918977468629258556813663637889) * 10 ^ 70 +
        8423042651996887247654100736394608752067494428433162136943092295790599) * 10 ^ 70 +
        2645637555604257095218304127850604673720187687807951750698668103333985) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (403 - x)) = _
  rw [show 404 = 254 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 20 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (404 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (404 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_404 :
    recurrence4Scalar1Exceptional.coeff 404 =
      -((((10630890357628869573997189333586264742675125450320083796 * 10 ^ 70 +
        4708911013415797979635283994625587040185285376615526246175552002977953) * 10 ^ 70 +
        0400590089619595385792239703239287382458138646596646443617469118879785) * 10 ^ 70 +
        8904752320755130127289299842391587158054496460537990470757988060778664) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (404 - x)) = _
  rw [show 405 = 255 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 19 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (405 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (405 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_405 :
    recurrence4Scalar1Exceptional.coeff 405 =
      ((((2343834116191918205561012511429857709108871600208225104 * 10 ^ 70 +
        3586357411997271169538165696263333601606843448134657018740414057367522) * 10 ^ 70 +
        7881847778726366785766898299813245820452224190187339873888106920420808) * 10 ^ 70 +
        2820587090078780963926584183607916899355478175140953023494905764895857) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (405 - x)) = _
  rw [show 406 = 256 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 18 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (406 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (406 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_406 :
    recurrence4Scalar1Exceptional.coeff 406 =
      -((((371140757639016852764663525729249864289555874711150941 * 10 ^ 70 +
        9966175715641742511316845465087101886259690467622264561106914046912438) * 10 ^ 70 +
        8679901248336225841123113254820655826435845608959817899105689875719249) * 10 ^ 70 +
        3219981570483710761145893040672001848780314381172956675346187872106210) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (406 - x)) = _
  rw [show 407 = 257 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 17 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (407 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (407 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_407 :
    recurrence4Scalar1Exceptional.coeff 407 =
      -((((4179776903337181702899687736177177798966855152737254 * 10 ^ 70 +
        0638398796394668250399716755638319235774369502405503850132894116792351) * 10 ^ 70 +
        2039628452474701959103291629389184857854397907585447908433951720213124) * 10 ^ 70 +
        0702342889974024151077458534035498412730767417015969322097405240907841) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (407 - x)) = _
  rw [show 408 = 258 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 16 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (408 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (408 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_408 :
    recurrence4Scalar1Exceptional.coeff 408 =
      ((((37871499151891776977905094566426317137059541136776991 * 10 ^ 70 +
        4818968247920960946700007606613910537705260982827420906058664157979399) * 10 ^ 70 +
        6413115590385753201611668660741031689524972205850070457632561210925171) * 10 ^ 70 +
        3962133598938730895850357709324129190339460013746083679148175455858972) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (408 - x)) = _
  rw [show 409 = 259 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 15 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (409 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (409 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_409 :
    recurrence4Scalar1Exceptional.coeff 409 =
      -((((22058724044786003272289880707200707343801787412166213 * 10 ^ 70 +
        3600861783489982435501699375266951401391894598530287945837354318882780) * 10 ^ 70 +
        5654631029032371543325413404837870975233517797902947211066747596852127) * 10 ^ 70 +
        5713164609468596689496764159233327305762435846400731282112473899874128) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (409 - x)) = _
  rw [show 410 = 260 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 14 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (410 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (410 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_410 :
    recurrence4Scalar1Exceptional.coeff 410 =
      ((((9499481198093857512162872527717470594622239728687209 * 10 ^ 70 +
        8555217875176420480594139041210337841539285258989100125455201396555317) * 10 ^ 70 +
        2440002359365833603463033680637983698228559728010800450811210848500887) * 10 ^ 70 +
        3349235007369676042920837986812197941624153654978250425502983987294244) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (410 - x)) = _
  rw [show 411 = 261 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 13 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (411 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (411 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_411 :
    recurrence4Scalar1Exceptional.coeff 411 =
      -((((3555202290760719948121732477398667450923584532280199 * 10 ^ 70 +
        6879018505742760846404601204124100612166784534491344325282736625464211) * 10 ^ 70 +
        5439763641207606908428993835590115362943884267712189912398358691357771) * 10 ^ 70 +
        7693201676977849928896273262228747240298843273539974791287913529407755) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (411 - x)) = _
  rw [show 412 = 262 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 12 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (412 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (412 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_412 :
    recurrence4Scalar1Exceptional.coeff 412 =
      ((((1215362965045628626595877710052963455947711583489689 * 10 ^ 70 +
        4843867028536757921468504880171073127097041146901099030939763921623192) * 10 ^ 70 +
        0263269930117468657871018427623719586824275211491491209825618540712476) * 10 ^ 70 +
        0891456836488287669706494288098345912974513574946758999803616676502408) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (412 - x)) = _
  rw [show 413 = 263 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 11 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (413 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (413 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_413 :
    recurrence4Scalar1Exceptional.coeff 413 =
      -((((386588626477770282663688183652080768449740360399103 * 10 ^ 70 +
        4044561221180753097027865002424074047210327007762438778215775632720617) * 10 ^ 70 +
        1915759691505847582740839701049538534325801380075490869734056747992888) * 10 ^ 70 +
        7841361821798241375238126848307540644522395216460719167671896220411831) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (413 - x)) = _
  rw [show 414 = 264 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 10 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (414 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (414 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_414 :
    recurrence4Scalar1Exceptional.coeff 414 =
      ((((114788289795616172326411093604011614578172901459461 * 10 ^ 70 +
        9146792576820886232691674126681434599941758811378699611194236083782534) * 10 ^ 70 +
        1849695129147619717303282515378300831340841221562362551224783040927675) * 10 ^ 70 +
        6368225077532317216961075777952417925007579353122887266415124135524031) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (414 - x)) = _
  rw [show 415 = 265 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 9 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (415 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (415 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_415 :
    recurrence4Scalar1Exceptional.coeff 415 =
      -((((31528693946067047190696998021302818699176193223555 * 10 ^ 70 +
        5000354625947778970026392979273739818975396932442926318372443305241933) * 10 ^ 70 +
        6947160449213154548921728908937326508111728458272497658670786073530870) * 10 ^ 70 +
        6486758462119539999853097443911218799780759234651149194985182679235362) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (415 - x)) = _
  rw [show 416 = 266 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 8 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (416 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (416 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_416 :
    recurrence4Scalar1Exceptional.coeff 416 =
      ((((7805210377499584586390186137753569331036170224619 * 10 ^ 70 +
        3856383241385114889108912616496523418661248584637440208418013867080877) * 10 ^ 70 +
        0876878610463118713394659152581889653397201485806672698164206267951051) * 10 ^ 70 +
        2207036496325196306743510192458136430992000071902619242164017158552581) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (416 - x)) = _
  rw [show 417 = 267 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 7 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (417 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (417 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_417 :
    recurrence4Scalar1Exceptional.coeff 417 =
      -((((1632201825788427607824254270402302180829874554758 * 10 ^ 70 +
        0566901357288232783344295473301311298648675310342336543173914780644549) * 10 ^ 70 +
        4674429646473234301545034675877668825626140905346485783455632754397762) * 10 ^ 70 +
        0712239906903364960312593074644372744229601600374198795165582770832368) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (417 - x)) = _
  rw [show 418 = 268 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 6 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (418 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (418 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_418 :
    recurrence4Scalar1Exceptional.coeff 418 =
      ((((229646858464208855609991224993346665936907028626 * 10 ^ 70 +
        7546846129076486959879065860698537914063192304301318512132638644494638) * 10 ^ 70 +
        3050021171216691577596836312448333705503114305960115861365105161956043) * 10 ^ 70 +
        1613774138724940955514183121177709300397046378461052681464571543857108) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (418 - x)) = _
  rw [show 419 = 269 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 5 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (419 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (419 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_419 :
    recurrence4Scalar1Exceptional.coeff 419 =
      ((((14906166062752847575398375007883590548500056834 * 10 ^ 70 +
        8826859386858396717427816855048824391760874412104125686375367805783652) * 10 ^ 70 +
        5506454149001280341316102509756533649302122509089267669248613376164433) * 10 ^ 70 +
        8267869514286672553165543986196175649093912180204719222221352208411704) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (419 - x)) = _
  rw [show 420 = 270 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 4 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (420 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (420 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_420 :
    recurrence4Scalar1Exceptional.coeff 420 =
      -((((28107570704229070251893648358544559368987238029 * 10 ^ 70 +
        1076402479061813761727435849921310900778855375871550261222667076714482) * 10 ^ 70 +
        5924554104074179455624809299977167190428227915511858509233192546900631) * 10 ^ 70 +
        4368220485589245083056599440908834935182698247889122413074368917810110) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (420 - x)) = _
  rw [show 421 = 271 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 3 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (421 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (421 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_421 :
    recurrence4Scalar1Exceptional.coeff 421 =
      ((((14055267887484909216365329410843879903000708225 * 10 ^ 70 +
        0384916899455587674903016437100054536117711510201331677368560325005810) * 10 ^ 70 +
        6143810873541117935252601780806304069995098887988803116580468116026112) * 10 ^ 70 +
        2648032871868934476524818899177807139655029266107368506034887766117141) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (421 - x)) = _
  rw [show 422 = 272 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 2 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (422 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (422 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_422 :
    recurrence4Scalar1Exceptional.coeff 422 =
      -((((5215455011020100220672632992726546026742592391 * 10 ^ 70 +
        2902117155863427170870019169634361170508026603391503595385763058522267) * 10 ^ 70 +
        2860890760370183838739575221806796568273604127486665992058047566642860) * 10 ^ 70 +
        9728689015996283575842542812983654364491402835820138085397881421532797) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (422 - x)) = _
  rw [show 423 = 273 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 1 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (423 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (423 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_423 :
    recurrence4Scalar1Exceptional.coeff 423 =
      ((((1620487035659883952558393865969755804595405109 * 10 ^ 70 +
        2029955013248110016505174759634443352658090798721802300856187044862154) * 10 ^ 70 +
        4894309499872207544987048573903232917152729291734935823782887015128282) * 10 ^ 70 +
        5979078042043379548741514147410060918705378931373767592040533685075504) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (423 - x)) = _
  rw [show 424 = 274 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (424 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (424 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_424 :
    recurrence4Scalar1Exceptional.coeff 424 =
      -((((433000701326570192726873723914192079348548012 * 10 ^ 70 +
        5350937451420036566858083798349680262480266476982753003077593789846799) * 10 ^ 70 +
        3219273113246443600784676904675051823732086366155628337800856936917273) * 10 ^ 70 +
        6204429098690189123879115250918411157078574724803297521729794244292694) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (424 - x)) = _
  rw [show 425 = 275 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 31 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (425 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (425 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_425 :
    recurrence4Scalar1Exceptional.coeff 425 =
      ((((98130426631790425371349657990438266643500166 * 10 ^ 70 +
        7210874139996085115985762916617276156028475217020490607292848796944918) * 10 ^ 70 +
        3107838649581777583792446253737831228319215871517578074653817384640357) * 10 ^ 70 +
        8930272626975819239016132542850503208796442190271886980097916273573770) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (425 - x)) = _
  rw [show 426 = 276 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 30 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (426 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (426 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_426 :
    recurrence4Scalar1Exceptional.coeff 426 =
      -((((17544280522269874746959822564310548520646990 * 10 ^ 70 +
        2343732795418728105501824513982762773719542526922321004446901356679101) * 10 ^ 70 +
        3664425409505030006123740021893242929929522231388612587250162486852776) * 10 ^ 70 +
        3175857075796055973603061842823203447804106623976700543212643703155305) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (426 - x)) = _
  rw [show 427 = 277 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 29 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (427 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (427 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_427 :
    recurrence4Scalar1Exceptional.coeff 427 =
      ((((1760476512681980908293505311713157595739720 * 10 ^ 70 +
        2868988006355432930506852340916067643745077167282394925612844553623586) * 10 ^ 70 +
        6369948803113774121454766780443518629435269023072531397016317457729306) * 10 ^ 70 +
        6551849481130553706259791648932789144041460562239035802282274473541042) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (427 - x)) = _
  rw [show 428 = 278 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 28 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (428 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (428 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_428 :
    recurrence4Scalar1Exceptional.coeff 428 =
      ((((311998602660962835503679879038921544757811 * 10 ^ 70 +
        7512346708922026827807464230366377187478955961780880247626506705185660) * 10 ^ 70 +
        6142432817921943534430534334586289032775121171608373509438720612092155) * 10 ^ 70 +
        2648736066374528466364205153205740071808704199947561071118351764596562) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (428 - x)) = _
  rw [show 429 = 279 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 27 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (429 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (429 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_429 :
    recurrence4Scalar1Exceptional.coeff 429 =
      -((((250055658455685951887203719413842516817311 * 10 ^ 70 +
        1031550544501815631229484513135813590714215776340932849763075571802896) * 10 ^ 70 +
        2233773431770387207511727104379982108111607150772632620743043074190345) * 10 ^ 70 +
        4171107440598502280681865001319594685664410633332621066605118679663406) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (429 - x)) = _
  rw [show 430 = 280 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 26 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (430 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (430 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_430 :
    recurrence4Scalar1Exceptional.coeff 430 =
      ((((92149887619617942403256440563558603520164 * 10 ^ 70 +
        3908953291948387253960676938777134763285361457997750401447816234750425) * 10 ^ 70 +
        1494537025853793570481591050280878069069485194363905957428937221261920) * 10 ^ 70 +
        6351332549742689864185775993376137323801839026911935691386211704227386) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (430 - x)) = _
  rw [show 431 = 281 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 25 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (431 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (431 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_431 :
    recurrence4Scalar1Exceptional.coeff 431 =
      -((((25619076018575652042899269163330090715828 * 10 ^ 70 +
        8226019942446012644856702714957669068723016543213235982387533555950427) * 10 ^ 70 +
        6580544263557858886188131283426992198090605277561276493205740693196049) * 10 ^ 70 +
        4424441472051443059784493935872641349809268304659275089055278219046847) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (431 - x)) = _
  rw [show 432 = 282 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 24 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (432 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (432 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_432 :
    recurrence4Scalar1Exceptional.coeff 432 =
      ((((5801800295820592280225309185174371928041 * 10 ^ 70 +
        7024016405097618668424424153308079191205901637558570609105179514757350) * 10 ^ 70 +
        1348950863230234364745281267171455372145189954395696568765248324301502) * 10 ^ 70 +
        2431999878553555104549772075116886740939532068578126734118318525432214) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (432 - x)) = _
  rw [show 433 = 283 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 23 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (433 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (433 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_433 :
    recurrence4Scalar1Exceptional.coeff 433 =
      -((((1060028683463009062327042931342829574638 * 10 ^ 70 +
        5865137130687288603639809916047179423764194426112696994898837613849067) * 10 ^ 70 +
        0594803921922026924154453831438914114927207589705079655976772373975401) * 10 ^ 70 +
        8612959699501945669445359408234490335576525340344340678927134857690567) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (433 - x)) = _
  rw [show 434 = 284 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 22 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (434 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (434 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_434 :
    recurrence4Scalar1Exceptional.coeff 434 =
      ((((139355044782029675086890997326256870614 * 10 ^ 70 +
        7717414555766047534739832295257035323444768759063728770295453692407591) * 10 ^ 70 +
        7855183108692378863627979136177423318082533524111090364756056386079897) * 10 ^ 70 +
        6786245356285429822604843926363437611779272627995201534327623552908887) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (434 - x)) = _
  rw [show 435 = 285 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 21 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (435 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (435 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_435 :
    recurrence4Scalar1Exceptional.coeff 435 =
      -((((5037621423046193383406106201527176383 * 10 ^ 70 +
        7261876931955883475692947790141305666580059820025357014788767459378952) * 10 ^ 70 +
        5202719819105489468500828851862851840587672579718655750106365910004231) * 10 ^ 70 +
        4388401920573081659426338137751703363550995875515616911158254472245053) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (435 - x)) = _
  rw [show 436 = 286 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 20 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (436 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (436 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_436 :
    recurrence4Scalar1Exceptional.coeff 436 =
      -((((4148240962641698544634593829956824831 * 10 ^ 70 +
        5057340928955671927100981871251628226620082007769866483509048377342329) * 10 ^ 70 +
        1945567134692296427473834680137545636127888503318407722032929158877579) * 10 ^ 70 +
        4423524479985137210949389039111014178101078594320198925109642778578756) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (436 - x)) = _
  rw [show 437 = 287 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 19 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (437 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (437 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_437 :
    recurrence4Scalar1Exceptional.coeff 437 =
      ((((1699601441764482925957020052803335214 * 10 ^ 70 +
        0589833685298152356464774109115229879990512884198339428293680099231420) * 10 ^ 70 +
        8850818988741219021902995044330511012043235973214568604102983092128801) * 10 ^ 70 +
        4799998068197470172090511389142123514648007151986610653002741650202036) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (437 - x)) = _
  rw [show 438 = 288 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 18 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (438 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (438 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_438 :
    recurrence4Scalar1Exceptional.coeff 438 =
      -((((432576591469643897976913756311177535 * 10 ^ 70 +
        0893948795331207510132908776794833579756291701768786162603574686323842) * 10 ^ 70 +
        4177109107601087646634721021799573806057138141806005667741397698356694) * 10 ^ 70 +
        7269152741811970254591630094103957299404307782212033540295744116519817) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (438 - x)) = _
  rw [show 439 = 289 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 17 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (439 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (439 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_439 :
    recurrence4Scalar1Exceptional.coeff 439 =
      ((((84102174282508588950402379521830004 * 10 ^ 70 +
        6716229818732434210651021596697649889930082693888024568459158376196832) * 10 ^ 70 +
        9742283818133813258168657950567174191780101549179816047931868440747058) * 10 ^ 70 +
        6531425894487147672731965221659118046440071017823489164850970620489304) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (439 - x)) = _
  rw [show 440 = 290 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 16 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (440 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (440 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_440 :
    recurrence4Scalar1Exceptional.coeff 440 =
      -((((12617419626235137403191928564000244 * 10 ^ 70 +
        5360101083924991738514975343826397555493325212749044516235541159194551) * 10 ^ 70 +
        9792335918255021362704079537443650985950547071651858976118751479446245) * 10 ^ 70 +
        5428309939760909481390728786460142151081754108318293816165802083752402) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (440 - x)) = _
  rw [show 441 = 291 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 15 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (441 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (441 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_441 :
    recurrence4Scalar1Exceptional.coeff 441 =
      ((((1271654009531225155265057890307414 * 10 ^ 70 +
        8511232760672105323742033776998725176591934121319751455555335570355940) * 10 ^ 70 +
        2369476545575026094957294594617433274277727964811189630952955758830964) * 10 ^ 70 +
        7304949495779525418904148399620932653292008946818625332325271995193250) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (441 - x)) = _
  rw [show 442 = 292 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 14 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (442 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (442 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_442 :
    recurrence4Scalar1Exceptional.coeff 442 =
      -((((7802870037849407743150414316537 * 10 ^ 70 +
        4426824733445706110958980960928765076703450883631688952587998377055170) * 10 ^ 70 +
        8856063418105476910181084494568359261893465462092904631433832437121459) * 10 ^ 70 +
        3971607533530504660774540602830763538890737985920971710604713366611153) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (442 - x)) = _
  rw [show 443 = 293 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 13 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (443 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (443 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_443 :
    recurrence4Scalar1Exceptional.coeff 443 =
      -((((32806415269919443532404799856793 * 10 ^ 70 +
        4853520244716431046124095685026941720090203457621334352250328553807123) * 10 ^ 70 +
        4773500390736042184453524381585902568022043841943198842271936783842800) * 10 ^ 70 +
        4628430535662864944846642407005754854624484997920028170078106019908909) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (443 - x)) = _
  rw [show 444 = 294 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 12 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (444 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (444 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_444 :
    recurrence4Scalar1Exceptional.coeff 444 =
      ((((9207453633963358917688553606499 * 10 ^ 70 +
        4412825899766125371616238931997674786433218874075684288858535068080566) * 10 ^ 70 +
        6818189513697978528567074612273567788534758216235308557211348414665295) * 10 ^ 70 +
        0982237351401138237740439201721524361831308727776529491106237900635847) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (444 - x)) = _
  rw [show 445 = 295 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 11 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (445 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (445 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_445 :
    recurrence4Scalar1Exceptional.coeff 445 =
      -((((1629302426243941884792072549694 * 10 ^ 70 +
        7731776115246366388150973344090636019078488420168684737337212630325063) * 10 ^ 70 +
        3450064742554913756180617105551205820626601296953957699892606519214207) * 10 ^ 70 +
        4760975658422485149497605422997260253004920802927777367942463856305335) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (445 - x)) = _
  rw [show 446 = 296 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 10 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (446 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (446 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_446 :
    recurrence4Scalar1Exceptional.coeff 446 =
      ((((201706345861152868432026041103 * 10 ^ 70 +
        7755750154904893000334317874544202961126012938873112145728529517470090) * 10 ^ 70 +
        6190644766986606201227904450103064976181867288314873764690923163671400) * 10 ^ 70 +
        6117920898915260242309169612419265558578603122294606023091480550443193) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (446 - x)) = _
  rw [show 447 = 297 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 9 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (447 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (447 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_447 :
    recurrence4Scalar1Exceptional.coeff 447 =
      -((((13899899343931369115249941161 * 10 ^ 70 +
        7418052510610879147287730130065656352637096118100496806452118288200981) * 10 ^ 70 +
        6251332647799318130989877948701857441488136047148295542637268881001578) * 10 ^ 70 +
        3275515917002958436101075042295285579473434533923369385080205088491459) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (447 - x)) = _
  rw [show 448 = 298 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 8 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (448 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (448 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_448 :
    recurrence4Scalar1Exceptional.coeff 448 =
      -((((859155597946695975895059669 * 10 ^ 70 +
        3774447701512187844274890708094456683877305325635395181272435619877367) * 10 ^ 70 +
        5856547485994626414360820506966682698638289499879326041264748458452412) * 10 ^ 70 +
        8025895918107153069194138604069611776561807706212393104311151084129053) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (448 - x)) = _
  rw [show 449 = 299 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 7 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (449 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (449 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_449 :
    recurrence4Scalar1Exceptional.coeff 449 =
      ((((460937769973201594768516897 * 10 ^ 70 +
        5494901571668900809178253746774658592826310274300672327026930789969867) * 10 ^ 70 +
        4076808268355153649903977943969214396668520964866148447307706473565432) * 10 ^ 70 +
        6810596017833914661465247771731587312687341632676078043759434380847545) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (449 - x)) = _
  rw [show 450 = 300 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 6 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (450 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (450 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_450 :
    recurrence4Scalar1Exceptional.coeff 450 =
      -((((84253638100569580973957126 * 10 ^ 70 +
        2448791284186527837958529817355880116053167172979081627771268646855792) * 10 ^ 70 +
        0824690731777107415484176698349084433582642344344332421463649339642287) * 10 ^ 70 +
        6757089739653758948194793703525481913967118301469065313359981378685486) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (450 - x)) = _
  rw [show 451 = 301 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 5 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (451 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (451 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_451 :
    recurrence4Scalar1Exceptional.coeff 451 =
      ((((9684363447359793663695879 * 10 ^ 70 +
        0578800172526876172244214054656510985499725239540584250867559833933169) * 10 ^ 70 +
        1400443514635015340138960889038666410897757870707942791914924794128819) * 10 ^ 70 +
        0703774333404414662471677448897702260828397586915635125461827193328567) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (451 - x)) = _
  rw [show 452 = 302 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 4 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (452 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (452 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_452 :
    recurrence4Scalar1Exceptional.coeff 452 =
      -((((591773154258722235983321 * 10 ^ 70 +
        7520425677440778528187413188908182704770857312371726043158148828707614) * 10 ^ 70 +
        7374493913723076433039738620833256405344734950469634241687095470752879) * 10 ^ 70 +
        1344451379173419218119409549133441958341346901443489060137110329832368) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (452 - x)) = _
  rw [show 453 = 303 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 3 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (453 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (453 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_453 :
    recurrence4Scalar1Exceptional.coeff 453 =
      -((((30106706837220651561452 * 10 ^ 70 +
        7000846649700216700266791542293112558643730580022697597057710980013590) * 10 ^ 70 +
        2769906361991804596087660396092051046775877899887365049154370729844355) * 10 ^ 70 +
        1846352846104939182582711892878692736914343525451511784494704092002434) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (453 - x)) = _
  rw [show 454 = 304 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 2 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (454 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (454 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_454 :
    recurrence4Scalar1Exceptional.coeff 454 =
      ((((13451691857470448473707 * 10 ^ 70 +
        0276440858501192151432379630503015838868431728403494284427189114438823) * 10 ^ 70 +
        7001685862463995251171396946186554614954854960154491569304849611295740) * 10 ^ 70 +
        4967502935146460460028414688353023408130335459801573132487436280558499) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (454 - x)) = _
  rw [show 455 = 305 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 1 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (455 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (455 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_455 :
    recurrence4Scalar1Exceptional.coeff 455 =
      -((((1911850557596787517993 * 10 ^ 70 +
        0512099012793519729352705773411006670550983728329409734365638894064625) * 10 ^ 70 +
        3161301411845766952088904589707723019691338741151226869820293005075308) * 10 ^ 70 +
        0803420162923167513616769278541616923940163119353559722086999121516569) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (455 - x)) = _
  rw [show 456 = 306 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (456 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (456 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_456 :
    recurrence4Scalar1Exceptional.coeff 456 =
      ((((151327952990464433343 * 10 ^ 70 +
        6848660218580961236377849005253299707582601680424262591267848706842156) * 10 ^ 70 +
        3345429424378525526148679946653575243099582049735922958728846013051822) * 10 ^ 70 +
        1469395862129231351401465495498207096573598438667177004452572462361153) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (456 - x)) = _
  rw [show 457 = 307 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 31 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (457 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (457 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_457 :
    recurrence4Scalar1Exceptional.coeff 457 =
      -((((2421565719705163545 * 10 ^ 70 +
        8530853885710339081106101498052577022369050236901292849521126001096872) * 10 ^ 70 +
        4595929930399642644455070597834331498140063795928781434248376523658637) * 10 ^ 70 +
        8299867001001550379940921715522841439416418115261711705142496953575039) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (457 - x)) = _
  rw [show 458 = 308 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 30 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (458 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (458 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_458 :
    recurrence4Scalar1Exceptional.coeff 458 =
      -((((1159882075880680663 * 10 ^ 70 +
        6177991783263941942547087105231269263389114686465703349221550395284304) * 10 ^ 70 +
        8335386703173334767639551752251849874950319115952483426265575759964416) * 10 ^ 70 +
        6451623138791142360780930577838288650076613459661060950394725441855867) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (458 - x)) = _
  rw [show 459 = 309 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 29 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (459 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (459 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_459 :
    recurrence4Scalar1Exceptional.coeff 459 =
      ((((178576555968421764 * 10 ^ 70 +
        6822656398144545550755335983764998781638128549295733072069604856788394) * 10 ^ 70 +
        2043190721006894067536604870146128391563599352502600541713696280512173) * 10 ^ 70 +
        3285277276348689988276114987402313321462540863269681566546317000672630) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (459 - x)) = _
  rw [show 460 = 310 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 28 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (460 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (460 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_460 :
    recurrence4Scalar1Exceptional.coeff 460 =
      -((((12730931210288179 * 10 ^ 70 +
        7512752298864473365188853336650801670045207185012611637442945804941967) * 10 ^ 70 +
        4296761405268428670415653103701015178826656000637355305056820147482204) * 10 ^ 70 +
        1157440951009116247417566810463037068028115687771876421614154436454168) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (460 - x)) = _
  rw [show 461 = 311 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 27 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (461 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (461 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_461 :
    recurrence4Scalar1Exceptional.coeff 461 =
      ((((109627124103007 * 10 ^ 70 +
        3847319186244893064606165571124297299984962396776207781661499257993517) * 10 ^ 70 +
        0839331312072012883740841345809626616000770070889006726528432135117146) * 10 ^ 70 +
        4664462524881750342710093663599673047378681389654334418522860763353458) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (461 - x)) = _
  rw [show 462 = 312 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 26 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (462 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (462 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_462 :
    recurrence4Scalar1Exceptional.coeff 462 =
      ((((79361601428302 * 10 ^ 70 +
        5822009749887516717005551592273685790697386311757012890049202726807966) * 10 ^ 70 +
        7433936318343660051682071515302700862551653943259650117633753664852788) * 10 ^ 70 +
        6820082106957771950405059114381902654630872303149685414570875351056882) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (462 - x)) = _
  rw [show 463 = 313 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 25 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (463 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (463 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_463 :
    recurrence4Scalar1Exceptional.coeff 463 =
      -((((8843060297664 * 10 ^ 70 +
        8325353416264147110994081650010326195784660685024224893754197827702834) * 10 ^ 70 +
        3606363707469766397177017248871774625029186052587143503132904468963661) * 10 ^ 70 +
        9994036759089488114510381548733019454645067817067516454085016376006115) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (463 - x)) = _
  rw [show 464 = 314 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 24 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (464 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (464 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_464 :
    recurrence4Scalar1Exceptional.coeff 464 =
      ((((358237517589 * 10 ^ 70 +
        3997283419741407734663961174799953172447112765613546415397179166944642) * 10 ^ 70 +
        9663521563804720650279484060314287045935048110443303168743651500210441) * 10 ^ 70 +
        4353256879387551263956390420480979242380369287471265714878039353726800) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (464 - x)) = _
  rw [show 465 = 315 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 23 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (465 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (465 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_465 :
    recurrence4Scalar1Exceptional.coeff 465 =
      ((((17433473663 * 10 ^ 70 +
        5064477574781163647814577148997398393404549489819233866524692633665731) * 10 ^ 70 +
        3702507961247296602634696923482231428770332334805902113982510658757810) * 10 ^ 70 +
        8203579836555561291194073524839751257465067289708146823243869465008029) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (465 - x)) = _
  rw [show 466 = 316 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 22 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (466 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (466 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_466 :
    recurrence4Scalar1Exceptional.coeff 466 =
      -((((3170784786 * 10 ^ 70 +
        2332912225758195758452039580819070640160121258301513645264750977637796) * 10 ^ 70 +
        8925994480279880395842338752636029272643363764936285657593472107257154) * 10 ^ 70 +
        4996521928932141667228593389143758204938098187658664929415213770061970) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (466 - x)) = _
  rw [show 467 = 317 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 21 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (467 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (467 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_467 :
    recurrence4Scalar1Exceptional.coeff 467 =
      ((((148792286 * 10 ^ 70 +
        5980903895155158028027947910383626100398937805195226784327831114715540) * 10 ^ 70 +
        6546511137467335129078904215467717048210886467698938550686674337230592) * 10 ^ 70 +
        1237456933024677964892678914852947407955622891372260806162036310989006) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (467 - x)) = _
  rw [show 468 = 318 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 20 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (468 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (468 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_468 :
    recurrence4Scalar1Exceptional.coeff 468 =
      ((((3386132 * 10 ^ 70 +
        9892209873401029579126046356117930938040546654626857583992655726739430) * 10 ^ 70 +
        8855688248425670354135882717415271078883448058900038635034628419846727) * 10 ^ 70 +
        9711437163530483082609472684181388902761163391009425864392263815005003) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (468 - x)) = _
  rw [show 469 = 319 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 19 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (469 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (469 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_469 :
    recurrence4Scalar1Exceptional.coeff 469 =
      -((((742119 * 10 ^ 70 +
        0678472644670985095895755881997689120694206793776030397900471794707427) * 10 ^ 70 +
        4895954661588434738306210785375810931708511886421580585508770741085694) * 10 ^ 70 +
        2952749263820107307025299123562713677437633203032551962990508331990636) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (469 - x)) = _
  rw [show 470 = 320 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 18 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (470 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (470 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_470 :
    recurrence4Scalar1Exceptional.coeff 470 =
      ((((25839 * 10 ^ 70 +
        3310408858395645383762570026529234517706286557099182529484051475798442) * 10 ^ 70 +
        2014571531209168361376913432198206936486854476434412331480563307396445) * 10 ^ 70 +
        7172384521656166393488725189056053296250023084705844769827852558307368) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (470 - x)) = _
  rw [show 471 = 321 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 17 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (471 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (471 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_471 :
    recurrence4Scalar1Exceptional.coeff 471 =
      ((((1099 * 10 ^ 70 +
        6317629491777711552831616804808818306190694855631479451570427246053989) * 10 ^ 70 +
        6308750221462750938719544557875781003375165647966304447455815784266442) * 10 ^ 70 +
        9370934903188757463836405995098015605328687158792267483403216342491574) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (471 - x)) = _
  rw [show 472 = 322 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 16 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (472 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (472 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_472 :
    recurrence4Scalar1Exceptional.coeff 472 =
      -((((108 * 10 ^ 70 +
        4972697791453582204347284223863341647685832936973986853865878957833737) * 10 ^ 70 +
        6828308556375838287761396229070963299081083309790144740468319839374889) * 10 ^ 70 +
        4084161215165187124836402012241193605201554791841620922285675310235411) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (472 - x)) = _
  rw [show 473 = 323 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 15 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (473 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (473 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_473 :
    recurrence4Scalar1Exceptional.coeff 473 =
      (((5667451028363976035077550494568203176653186889462620253492812546633629 * 10 ^ 70 +
        2986726253339470288533727956458124255560728112256907195192180473461160) * 10 ^ 70 +
        1342140559918573497147158337728584873857296546491422336263951847747852) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (473 - x)) = _
  rw [show 474 = 324 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 14 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (474 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (474 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_474 :
    recurrence4Scalar1Exceptional.coeff 474 =
      (((2168692204379747848199723358282715236230903034569488728216737389388318 * 10 ^ 70 +
        5375196616854925757382635465387447042843480161524260782492236289901807) * 10 ^ 70 +
        0994464934625610138854741714071986507302987954697120876765686163924716) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (474 - x)) = _
  rw [show 475 = 325 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 13 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (475 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (475 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_475 :
    recurrence4Scalar1Exceptional.coeff 475 =
      -(((45990075860489582893381791059194114731099269732470019876839831345593 * 10 ^ 70 +
        4804897259986769464189140438516186345388753147333514335091007779575799) * 10 ^ 70 +
        7426323652016413326301380157464076127736004623883315392941167510201877) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (475 - x)) = _
  rw [show 476 = 326 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 12 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (476 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (476 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_476 :
    recurrence4Scalar1Exceptional.coeff 476 =
      -(((3156060433670065619328225879692325890279038183323999169121177067843 * 10 ^ 70 +
        5383734457679116547683519145790692363549444317815532193291641320070125) * 10 ^ 70 +
        3496963682411849065860110990205149368853358172935858903913212304637825) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (476 - x)) = _
  rw [show 477 = 327 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 11 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (477 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (477 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_477 :
    recurrence4Scalar1Exceptional.coeff 477 =
      (((80125690147855018644270650229550049709695690891728734550632303462 * 10 ^ 70 +
        1638775290758582736990379839724309515424508121581465452673675137188810) * 10 ^ 70 +
        0660669965240481449448723622845579408646360621103946854923060911405224) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (477 - x)) = _
  rw [show 478 = 328 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 10 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (478 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (478 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_478 :
    recurrence4Scalar1Exceptional.coeff 478 =
      (((4269811907579749141997586763313639205922843288374886295677766558 * 10 ^ 70 +
        2632960483308507846946420942242854698008997963345557562516436005546173) * 10 ^ 70 +
        4091942435817734987381366271009338357486174830436761216247729535652557) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (478 - x)) = _
  rw [show 479 = 329 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 9 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (479 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (479 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_479 :
    recurrence4Scalar1Exceptional.coeff 479 =
      -(((58330672301131239365497806399289902117134742371015606444904545 * 10 ^ 70 +
        6731167955439490456184403152374590941000016308207588636771056793069223) * 10 ^ 70 +
        1176537025134688514838511045080083342937546849130205026886012251780556) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (479 - x)) = _
  rw [show 480 = 330 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 8 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_479_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (480 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (480 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_480 :
    recurrence4Scalar1Exceptional.coeff 480 =
      -(((5077389193269732359675298544962926879861679155265635905201498 * 10 ^ 70 +
        0397119998228922851351531370703449590874137340222027595143424586809499) * 10 ^ 70 +
        4348548255638297150141858366900770362999123959966227963520793959765611) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (480 - x)) = _
  rw [show 481 = 331 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 7 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_480_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (481 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (481 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_481 :
    recurrence4Scalar1Exceptional.coeff 481 =
      -(((44314752784628604038936492935738752314484713728336606701504 * 10 ^ 70 +
        8138671782391326840040584112730626240379705083230885727228445937826841) * 10 ^ 70 +
        6272219464158548378228789032746511904048044933047980024412523010879465) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (481 - x)) = _
  rw [show 482 = 332 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 6 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_481_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (482 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (482 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_482 :
    recurrence4Scalar1Exceptional.coeff 482 =
      (((2843144209820886122213137969581903119891099228271814613955 * 10 ^ 70 +
        0313858717062534976670299625914507001316090111948580230881750702915353) * 10 ^ 70 +
        2414426210466922020786022580226935039587154616131808252871835616857070) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (482 - x)) = _
  rw [show 483 = 333 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 5 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_482_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (483 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (483 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_483 :
    recurrence4Scalar1Exceptional.coeff 483 =
      (((112525381270924657698311394151515330138594674182318301353 * 10 ^ 70 +
        8873793556326748193605982669933733310360188603324759858232273799729851) * 10 ^ 70 +
        5025991958710342984402047658262389815080484142034908671933383947089342) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (483 - x)) = _
  rw [show 484 = 334 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 4 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_483_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (484 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (484 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_484 :
    recurrence4Scalar1Exceptional.coeff 484 =
      (((2166947783736965217425565816670288068923863876817644565 * 10 ^ 70 +
        8202772094702821305488330698723237889251434614707399344191006150342035) * 10 ^ 70 +
        1073385183888527820723615474436584147288487428970578390382572178759997) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (484 - x)) = _
  rw [show 485 = 335 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 3 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_484_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (485 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (485 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_485 :
    recurrence4Scalar1Exceptional.coeff 485 =
      (((27187968953627444223152573569572420122568063980747766 * 10 ^ 70 +
        5905136508453575757490819927496318015208155636388796174017787747161477) * 10 ^ 70 +
        5225676051704165008285948876762313457716753854924554771617443502994044) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (485 - x)) = _
  rw [show 486 = 336 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 2 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_485_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (486 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (486 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_486 :
    recurrence4Scalar1Exceptional.coeff 486 =
      (((240755074531439446965310236854693306256644850626543 * 10 ^ 70 +
        5608290531719289992432533024835455012706907437626573342317944435588614) * 10 ^ 70 +
        6460736695831188149551570819552318599371015379198782848230547954378314) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (486 - x)) = _
  rw [show 487 = 337 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 1 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_486_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (487 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (487 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_487 :
    recurrence4Scalar1Exceptional.coeff 487 =
      (((1541351404048283121527118032443867301144779852343 * 10 ^ 70 +
        8166142141385985732267928472384396206089829621700018170417274187387658) * 10 ^ 70 +
        2467271307478840118530285207902734518002097769905287245651500313324309) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (487 - x)) = _
  rw [show 488 = 338 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_487_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (488 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (488 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_488 :
    recurrence4Scalar1Exceptional.coeff 488 =
      (((7052193786184947062440606805634473979258347742 * 10 ^ 70 +
        4937028591276762527160408556683390616041131415393051508069417352623368) * 10 ^ 70 +
        8821954031192548041518310112434569340001407881700490557577496040477408) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (488 - x)) = _
  rw [show 489 = 339 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 31 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_488_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (489 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (489 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_489 :
    recurrence4Scalar1Exceptional.coeff 489 =
      (((21527082623454426325753588628138865183415668 * 10 ^ 70 +
        7628310142049445199890245756986300926794126813917114769721237130907947) * 10 ^ 70 +
        0812923752057928296591707806027666706101121958565647990259982478381643) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (489 - x)) = _
  rw [show 490 = 340 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 30 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_489_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (490 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (490 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_490 :
    recurrence4Scalar1Exceptional.coeff 490 =
      (((32216482565032211172939792304105410073034 * 10 ^ 70 +
        1911619588559341222509442762896801468145970034055150388431410297218767) * 10 ^ 70 +
        1958365694451720576576371297877992185384053964269398291758904109457610) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (490 - x)) = _
  rw [show 491 = 341 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 29 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_490_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (491 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (491 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_491 :
    recurrence4Scalar1Exceptional.coeff 491 =
      -(((50494670848919734936943857332063033211 * 10 ^ 70 +
        3607165084757063449696303411523925357989688767054543019985655727820316) * 10 ^ 70 +
        5828247915353020129584730414162885347276064742066268125536382650443862) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (491 - x)) = _
  rw [show 492 = 342 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 28 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_491_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (492 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (492 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_492 :
    recurrence4Scalar1Exceptional.coeff 492 =
      -(((413086113675693471732150534407229610 * 10 ^ 70 +
        7274155265708701865095359345872731826350294673549693338723255664727918) * 10 ^ 70 +
        0757450187287597138897000407073667519447686502426017557825885810593168) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (492 - x)) = _
  rw [show 493 = 343 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 27 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_492_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (493 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (493 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_493 :
    recurrence4Scalar1Exceptional.coeff 493 =
      -(((1004977720854509949826324601814341 * 10 ^ 70 +
        9326090735770029768943336668354191613781423880685607317855051342352533) * 10 ^ 70 +
        7223504492271179404244209442784677859868904055830350768627935533077595) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (493 - x)) = _
  rw [show 494 = 344 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 26 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_493_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (494 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (494 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_494 :
    recurrence4Scalar1Exceptional.coeff 494 =
      -(((777005247554678474934625686294 * 10 ^ 70 +
        8302091229313092135295700943293423043379381454113005398976042265414048) * 10 ^ 70 +
        4883172309658176261921001848450028087267883865326161482288750689620533) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (494 - x)) = _
  rw [show 495 = 345 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 25 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_494_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (495 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (495 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_495 :
    recurrence4Scalar1Exceptional.coeff 495 =
      (((2077598761867885242197160992 * 10 ^ 70 +
        1530073683414790412457504308106874271336443067374594463988139282770027) * 10 ^ 70 +
        8744813183370935829032456866242316225992024191242220584228521984619298) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (495 - x)) = _
  rw [show 496 = 346 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 24 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_495_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (496 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (496 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_496 :
    recurrence4Scalar1Exceptional.coeff 496 =
      (((6990527602315234363812674 * 10 ^ 70 +
        9495825261890558850168608190476978128786755951929665927231806847444251) * 10 ^ 70 +
        6279901520097627933987810221753343164183654107639422242809311220835612) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (496 - x)) = _
  rw [show 497 = 347 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 23 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_496_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (497 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (497 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_497 :
    recurrence4Scalar1Exceptional.coeff 497 =
      (((8236069363469570462612 * 10 ^ 70 +
        2496838704996183382493989033229184623313254181489035492834396145079479) * 10 ^ 70 +
        0498760473909041829273851348344545267350155457397169022476582145368250) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (497 - x)) = _
  rw [show 498 = 348 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 22 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_497_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (498 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (498 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_498 :
    recurrence4Scalar1Exceptional.coeff 498 =
      (((182295829531068640 * 10 ^ 70 +
        1226613352072457971330335172722011220287528150662886758716073062417904) * 10 ^ 70 +
        4237282099589638849767835489938385707336970986331900650928528856197426) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (498 - x)) = _
  rw [show 499 = 349 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 21 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_498_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (499 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (499 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_499 :
    recurrence4Scalar1Exceptional.coeff 499 =
      -(((13022683892161728 * 10 ^ 70 +
        4221127560277218785709340217264950809575763065432801590926684640216559) * 10 ^ 70 +
        5810300660910590937049010074168646708336144383815102749213107198283803) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (499 - x)) = _
  rw [show 500 = 350 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 20 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_499_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (500 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (500 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_500 :
    recurrence4Scalar1Exceptional.coeff 500 =
      -(((20004262161907 * 10 ^ 70 +
        2900499548199670581410852817094641975346312818985216875359486484379858) * 10 ^ 70 +
        3763330316657124060609451897092832910287277496705520026202364855012637) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (500 - x)) = _
  rw [show 501 = 351 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 19 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_500_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (501 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (501 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_501 :
    recurrence4Scalar1Exceptional.coeff 501 =
      -(((16361716441 * 10 ^ 70 +
        4739234462527237199365301810525359155564791273510731011981589175604820) * 10 ^ 70 +
        8197368743682355547778479588435586800825253619785567922346752297622793) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (501 - x)) = _
  rw [show 502 = 352 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 18 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_501_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (502 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (502 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_502 :
    recurrence4Scalar1Exceptional.coeff 502 =
      -(((8388643 * 10 ^ 70 +
        2581234468965957586400792723397635868812389400440769936594706799057583) * 10 ^ 70 +
        0843863464504985145140145499226460320049879299584920519915439170480554) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (502 - x)) = _
  rw [show 503 = 353 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 17 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_502_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (503 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (503 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_503 :
    recurrence4Scalar1Exceptional.coeff 503 =
      -(((2799 * 10 ^ 70 +
        6079143778576366052722778304249361322256942719530062313826294782017586) * 10 ^ 70 +
        4468783802922050229408962859595161289218288401169693787775302570393003) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (503 - x)) = _
  rw [show 504 = 354 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 16 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_503_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (504 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (504 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_504 :
    recurrence4Scalar1Exceptional.coeff 504 =
      -((6109193959875492613217762191327105719816050549190561136871640373188092 * 10 ^ 70 +
        6106556521441313543609267624560287155663760534341735567316053918198285) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (504 - x)) = _
  rw [show 505 = 355 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 15 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_504_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (505 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (505 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_505 :
    recurrence4Scalar1Exceptional.coeff 505 =
      -((863338868337357292475927918374825849054006949194948128604447748018 * 10 ^ 70 +
        0521070065923223262512031336587193787063404809310199835794619890340794) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (505 - x)) = _
  rw [show 506 = 356 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 14 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_505_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (506 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (506 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_506 :
    recurrence4Scalar1Exceptional.coeff 506 =
      -((77602786403100490945174840057444589387398187416328328022261666 * 10 ^ 70 +
        7806704759803378703882722836285033022276501742672910874229310664333172) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (506 - x)) = _
  rw [show 507 = 357 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 13 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_506_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (507 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (507 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_507 :
    recurrence4Scalar1Exceptional.coeff 507 =
      -((4322518835459384159700204986761387825032459972649549810066 * 10 ^ 70 +
        6981359555666194155545769348363771676414813663242397996029795128510784) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (507 - x)) = _
  rw [show 508 = 358 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 12 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_507_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (508 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (508 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_508 :
    recurrence4Scalar1Exceptional.coeff 508 =
      -((144503823728056919378650079468546482732575531222641160 * 10 ^ 70 +
        4561032415874467445003105222849956155965997080022800352214250810875515) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (508 - x)) = _
  rw [show 509 = 359 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 11 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_508_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (509 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (509 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (509 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_509 :
    recurrence4Scalar1Exceptional.coeff 509 =
      -((2820709068956917334074195430984676809012815266731 * 10 ^ 70 +
        1948456508759938494618995930089800432157543577425249331192981165325925) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (509 - x)) = _
  rw [show 510 = 360 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 10 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_509_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (510 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (510 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (510 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_510 :
    recurrence4Scalar1Exceptional.coeff 510 =
      -((30800353397030362031170255000043524407004655 * 10 ^ 70 +
        2686827164956846414725643805630626682674296491979401404858709298222416) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (510 - x)) = _
  rw [show 511 = 361 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 9 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_510_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (511 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (511 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (511 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_511 :
    recurrence4Scalar1Exceptional.coeff 511 =
      -((175895633707345746905372989650870272753 * 10 ^ 70 +
        8376086258387496535536079165034235073800945558094680878147946099306650) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (511 - x)) = _
  rw [show 512 = 362 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 8 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_511_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (512 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (512 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (512 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_512 :
    recurrence4Scalar1Exceptional.coeff 512 =
      -((502328471793129300987077794232758 * 10 ^ 70 +
        7548221748685469362570094423716559747201199484216595596187644876685931) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (512 - x)) = _
  rw [show 513 = 363 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 7 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_512_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 364,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (513 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient1.coeff (513 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 370 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (370 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (513 - (370 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_513 :
    recurrence4Scalar1Exceptional.coeff 513 =
      -((662685707319367918171916930 * 10 ^ 70 +
        0119008155598713598057211780087610073542258076228772771250407486983938) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (513 - x)) = _
  rw [show 514 = 364 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 6 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_513_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
