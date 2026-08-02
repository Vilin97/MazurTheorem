/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C2_coeff_10
  recurrence4C2_coeff_100
  recurrence4C2_coeff_101
  recurrence4C2_coeff_102
  recurrence4C2_coeff_103
  recurrence4C2_coeff_104
  recurrence4C2_coeff_105
  recurrence4C2_coeff_106
  recurrence4C2_coeff_107
  recurrence4C2_coeff_108
  recurrence4C2_coeff_109
  recurrence4C2_coeff_11
  recurrence4C2_coeff_110
  recurrence4C2_coeff_111
  recurrence4C2_coeff_112
  recurrence4C2_coeff_113
  recurrence4C2_coeff_114
  recurrence4C2_coeff_115
  recurrence4C2_coeff_116
  recurrence4C2_coeff_117
  recurrence4C2_coeff_118
  recurrence4C2_coeff_119
  recurrence4C2_coeff_12
  recurrence4C2_coeff_120
  recurrence4C2_coeff_121
  recurrence4C2_coeff_122
  recurrence4C2_coeff_123
  recurrence4C2_coeff_124
  recurrence4C2_coeff_125
  recurrence4C2_coeff_126
  recurrence4C2_coeff_127
  recurrence4C2_coeff_128
  recurrence4C2_coeff_129
  recurrence4C2_coeff_13
  recurrence4C2_coeff_130
  recurrence4C2_coeff_131
  recurrence4C2_coeff_132
  recurrence4C2_coeff_133
  recurrence4C2_coeff_134
  recurrence4C2_coeff_135
  recurrence4C2_coeff_136
  recurrence4C2_coeff_137
  recurrence4C2_coeff_138
  recurrence4C2_coeff_139
  recurrence4C2_coeff_14
  recurrence4C2_coeff_140
  recurrence4C2_coeff_141
  recurrence4C2_coeff_142
  recurrence4C2_coeff_143
  recurrence4C2_coeff_144
  recurrence4C2_coeff_145
  recurrence4C2_coeff_15
  recurrence4C2_coeff_16
  recurrence4C2_coeff_17
  recurrence4C2_coeff_18
  recurrence4C2_coeff_19
  recurrence4C2_coeff_20
  recurrence4C2_coeff_21
  recurrence4C2_coeff_22
  recurrence4C2_coeff_23
  recurrence4C2_coeff_24
  recurrence4C2_coeff_25
  recurrence4C2_coeff_26
  recurrence4C2_coeff_27

attribute [local simp]
  recurrence4C2_coeff_28
  recurrence4C2_coeff_29
  recurrence4C2_coeff_3
  recurrence4C2_coeff_30
  recurrence4C2_coeff_31
  recurrence4C2_coeff_32
  recurrence4C2_coeff_33
  recurrence4C2_coeff_34
  recurrence4C2_coeff_35
  recurrence4C2_coeff_36
  recurrence4C2_coeff_37
  recurrence4C2_coeff_38
  recurrence4C2_coeff_39
  recurrence4C2_coeff_4
  recurrence4C2_coeff_40
  recurrence4C2_coeff_41
  recurrence4C2_coeff_42
  recurrence4C2_coeff_43
  recurrence4C2_coeff_44
  recurrence4C2_coeff_45
  recurrence4C2_coeff_46
  recurrence4C2_coeff_47
  recurrence4C2_coeff_48
  recurrence4C2_coeff_49
  recurrence4C2_coeff_5
  recurrence4C2_coeff_50
  recurrence4C2_coeff_51
  recurrence4C2_coeff_52
  recurrence4C2_coeff_53
  recurrence4C2_coeff_54
  recurrence4C2_coeff_55
  recurrence4C2_coeff_56
  recurrence4C2_coeff_57
  recurrence4C2_coeff_58
  recurrence4C2_coeff_59
  recurrence4C2_coeff_6
  recurrence4C2_coeff_60
  recurrence4C2_coeff_61
  recurrence4C2_coeff_62
  recurrence4C2_coeff_63
  recurrence4C2_coeff_64
  recurrence4C2_coeff_65
  recurrence4C2_coeff_66
  recurrence4C2_coeff_67
  recurrence4C2_coeff_68
  recurrence4C2_coeff_69
  recurrence4C2_coeff_7
  recurrence4C2_coeff_70
  recurrence4C2_coeff_71
  recurrence4C2_coeff_72
  recurrence4C2_coeff_73
  recurrence4C2_coeff_74
  recurrence4C2_coeff_75
  recurrence4C2_coeff_76
  recurrence4C2_coeff_77
  recurrence4C2_coeff_78
  recurrence4C2_coeff_79
  recurrence4C2_coeff_8
  recurrence4C2_coeff_80
  recurrence4C2_coeff_81
  recurrence4C2_coeff_82
  recurrence4C2_coeff_83
  recurrence4C2_coeff_84
  recurrence4C2_coeff_85

attribute [local simp]
  recurrence4C2_coeff_86
  recurrence4C2_coeff_87
  recurrence4C2_coeff_88
  recurrence4C2_coeff_89
  recurrence4C2_coeff_9
  recurrence4C2_coeff_90
  recurrence4C2_coeff_91
  recurrence4C2_coeff_92
  recurrence4C2_coeff_93
  recurrence4C2_coeff_94
  recurrence4C2_coeff_95
  recurrence4C2_coeff_96
  recurrence4C2_coeff_97
  recurrence4C2_coeff_98
  recurrence4C2_coeff_99
  recurrence4ExceptionalProduct_coeff_227
  recurrence4ExceptionalProduct_coeff_228
  recurrence4ExceptionalProduct_coeff_229
  recurrence4ExceptionalProduct_coeff_230
  recurrence4ExceptionalProduct_coeff_231
  recurrence4ExceptionalProduct_coeff_232
  recurrence4ExceptionalProduct_coeff_233
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar2Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (372 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_372 :
    recurrence4Scalar2Exceptional.coeff 372 =
      -((((151262134404461584991576736302996011491460542890059538120846883612916 * 10 ^ 70 +
        5078697638414433652558579338787584018302151305146966462429324615364966) * 10 ^ 70 +
        0363633096529021941892408049509544759738055216627738262425462717217078) * 10 ^ 70 +
        8185968279442471402251386954140854752968416242789466624177950882104448) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (372 - x)) = _
  rw [show 373 = 227 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 15 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (373 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_373 :
    recurrence4Scalar2Exceptional.coeff 373 =
      ((((58434432547249241623092728275209397534392921308070658943863957417467 * 10 ^ 70 +
        3242817485553346319074155675196550753008207785456143746652600577916634) * 10 ^ 70 +
        7017602304016085037545953213466475769413872289918346212738936939140716) * 10 ^ 70 +
        6276096467351364258826939222857968002377183231662140144137745294353370) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (373 - x)) = _
  rw [show 374 = 228 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 14 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (374 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_374 :
    recurrence4Scalar2Exceptional.coeff 374 =
      -((((22039717858705707427176884549795596661283928964018409351714259768766 * 10 ^ 70 +
        3498924232821707264827223958414075700045079223719394806479703277147031) * 10 ^ 70 +
        2376667282025422197001527394033348643679182435762430252838701040640852) * 10 ^ 70 +
        7992479144708038355290623517244620544429488610197045112799714144970397) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (374 - x)) = _
  rw [show 375 = 229 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 13 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (375 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_375 :
    recurrence4Scalar2Exceptional.coeff 375 =
      ((((8106666028232103212518394403928549911375739068947058527237206759835 * 10 ^ 70 +
        5920602406382787146551229848437289047358069366869452088747715880957024) * 10 ^ 70 +
        3687607796444744542465616039226674125577423794103931145700452913590843) * 10 ^ 70 +
        4332577045933332724711203779231905010228967558357356513005095640746701) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (375 - x)) = _
  rw [show 376 = 230 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 12 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (376 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_376 :
    recurrence4Scalar2Exceptional.coeff 376 =
      -((((2900889101857711105010822409102347570679690588852817252791166686555 * 10 ^ 70 +
        1708594594281549279320573217835048110346001755110156506999249599623107) * 10 ^ 70 +
        7015762789456828393250798750780177358774636105923778459005476473462493) * 10 ^ 70 +
        8770041601353131772903479745208280773560439952862187773468379758204065) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (376 - x)) = _
  rw [show 377 = 231 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 11 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (377 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_377 :
    recurrence4Scalar2Exceptional.coeff 377 =
      ((((1005469742690826664974217669741811543799042674949465046532113529338 * 10 ^ 70 +
        0963643432563404649002344266512526707606883697272701847692887086541819) * 10 ^ 70 +
        2804652023147160917594659004338141768678407460277340179665865182415624) * 10 ^ 70 +
        6808422853339248457965546145922382096888086380690475170145043073980602) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (377 - x)) = _
  rw [show 378 = 232 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 10 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (378 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_378 :
    recurrence4Scalar2Exceptional.coeff 378 =
      -((((334951692869969801281181548656706023584790451871344407299508842740 * 10 ^ 70 +
        5698971291905886495060512819950614664684644656932023463822583180403422) * 10 ^ 70 +
        3763033490562227452034538231419573492891374409396991414217896219624522) * 10 ^ 70 +
        6146360131799402556248043506695521172400952768670398624544355829697737) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (378 - x)) = _
  rw [show 379 = 233 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 9 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (379 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_379 :
    recurrence4Scalar2Exceptional.coeff 379 =
      ((((105727348760877209411410393268191567034445437187338095509249621141 * 10 ^ 70 +
        5807061483171012976585529114118309555041499722917262596962449414972411) * 10 ^ 70 +
        2546252388612484337361774931328473207649808775986913176135136614257446) * 10 ^ 70 +
        8375048771268398874513402462338765184338439184948828222302636661517599) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (379 - x)) = _
  rw [show 380 = 234 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 8 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (380 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_380 :
    recurrence4Scalar2Exceptional.coeff 380 =
      -((((30728392952763784681131675382877104352247251749271458922012464259 * 10 ^ 70 +
        8737419517175853714640260869232991610828655160657772103424459287596259) * 10 ^ 70 +
        5972708330482204627087493713949661879464225332858953855393006183728825) * 10 ^ 70 +
        6716364322267409982172502619089466421790715882056257712434251132220448) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (380 - x)) = _
  rw [show 381 = 235 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 7 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (381 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_381 :
    recurrence4Scalar2Exceptional.coeff 381 =
      ((((7668596523963274574653699431088823851958165747656330513440200273 * 10 ^ 70 +
        9233786777761262258648001652689715849210152813760682182405309351085481) * 10 ^ 70 +
        5031945297477290838639558981387498376528408650452876656836147319244369) * 10 ^ 70 +
        3780253525073232167478201653591260762920069997313504695727760572514475) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (381 - x)) = _
  rw [show 382 = 236 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 6 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (382 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_382 :
    recurrence4Scalar2Exceptional.coeff 382 =
      -((((1260600002092625920006964453827012001502225450139047013342353463 * 10 ^ 70 +
        9007832894464244587500649526248527730799966281392117783540864151882270) * 10 ^ 70 +
        1544694486803736373712438920067646882212251630025153348837544903191735) * 10 ^ 70 +
        6101791909789693970879555875363402702099430109701406201366718094656641) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (382 - x)) = _
  rw [show 383 = 237 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 5 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (383 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_383 :
    recurrence4Scalar2Exceptional.coeff 383 =
      -((((185151365003776616612885805392194123835336961276400145760970161 * 10 ^ 70 +
        1760763357812621469072802002146881539091368880038942296946017539266220) * 10 ^ 70 +
        3188385831594384132587780825363957145156000834250063917261735251120720) * 10 ^ 70 +
        3887198078758932415397955672612471778144757775880745552490301776013710) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (383 - x)) = _
  rw [show 384 = 238 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 4 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (384 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_384 :
    recurrence4Scalar2Exceptional.coeff 384 =
      ((((329878406346372431310445236154932530498356709330438040446380161 * 10 ^ 70 +
        9897404052487676087967110798268610788353040997988629186448006880600961) * 10 ^ 70 +
        4384350872308674860227641796059834192445186484011854852452153895463380) * 10 ^ 70 +
        1026788778897882120086254097404849221517212542923367821749405177108173) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (384 - x)) = _
  rw [show 385 = 239 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 3 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (385 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_385 :
    recurrence4Scalar2Exceptional.coeff 385 =
      -((((223689989204169894001618848807108788454183751541959971716590006 * 10 ^ 70 +
        6167815415687774239642531242264697706875641712107904655354441297586134) * 10 ^ 70 +
        0732910997575551536046459313920947227331301779103880231440682002112274) * 10 ^ 70 +
        2774904209732425840593017574132743283296902023077439138099903564159794) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (385 - x)) = _
  rw [show 386 = 240 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 2 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (386 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_386 :
    recurrence4Scalar2Exceptional.coeff 386 =
      ((((120945726165492879076974869951154946065908951330436713615522972 * 10 ^ 70 +
        9306911665924692615634919783992864874678087124954928835144262518093467) * 10 ^ 70 +
        2296036548890886744945783088715475152018216731147322573707221870268510) * 10 ^ 70 +
        5939443740050360568679045158478385596918947079252419465574261773694082) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (386 - x)) = _
  rw [show 387 = 241 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 1 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (387 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_387 :
    recurrence4Scalar2Exceptional.coeff 387 =
      -((((58528901039448786064170755383764590778372701486740537438717298 * 10 ^ 70 +
        1024540127449233322989910033293935932906965218189468673081448724815298) * 10 ^ 70 +
        8642216424045447644247812828442319415045545630008621046049761942151570) * 10 ^ 70 +
        3431896881493008777205857905859686636082554256998360337065025270828622) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (387 - x)) = _
  rw [show 388 = 242 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (388 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_388 :
    recurrence4Scalar2Exceptional.coeff 388 =
      ((((26390654936468430994296895420936147266072111035239551875472329 * 10 ^ 70 +
        4755315418581980524709884425815154413778124183921305893139321127116611) * 10 ^ 70 +
        0092854037424452660172419142809804305250607087738407587645945939042507) * 10 ^ 70 +
        2652727296446983743258962298872827004609164768665175355330706011787001) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (388 - x)) = _
  rw [show 389 = 243 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 31 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (389 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_389 :
    recurrence4Scalar2Exceptional.coeff 389 =
      -((((11290994987320653649236542420161149305942559773375900052486489 * 10 ^ 70 +
        6905239850341490274290742709741052857108877684536698307737004382122897) * 10 ^ 70 +
        1367855918876046852967745512648460382708359728363549612910565471142949) * 10 ^ 70 +
        7617408432812232464731956245781395602309816346470044955962031387318626) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (389 - x)) = _
  rw [show 390 = 244 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 30 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (390 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_390 :
    recurrence4Scalar2Exceptional.coeff 390 =
      ((((4626536040348961521587719103780547094387692469526614552851620 * 10 ^ 70 +
        2543954502874210932776965929718147944993268077331704307597265446229215) * 10 ^ 70 +
        3578481385465154325590587631681265112522134159312400838203756416429186) * 10 ^ 70 +
        2599784855778047031622707860091440243572092039178448721763199160635592) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (390 - x)) = _
  rw [show 391 = 245 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 29 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (391 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_391 :
    recurrence4Scalar2Exceptional.coeff 391 =
      -((((1824603463841755346485198434060193207280858270314310748977158 * 10 ^ 70 +
        8079553071644463506033340389213793811626151038763659532187247203355842) * 10 ^ 70 +
        1572761179529835479273849723640068959580271938089883980334141875002160) * 10 ^ 70 +
        2417226256913277063349571712213155364350862084315995287908408629918958) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (391 - x)) = _
  rw [show 392 = 246 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 28 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (392 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_392 :
    recurrence4Scalar2Exceptional.coeff 392 =
      ((((694292167122956718061301904217055315198574368711840062427488 * 10 ^ 70 +
        8149708776794052967656450329654195666132383832773931398020183561511020) * 10 ^ 70 +
        2757404056547679153594115382412674217833036868799731771326898917311004) * 10 ^ 70 +
        3713469836443824582592092442556815416760584518750973571911976156848869) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (392 - x)) = _
  rw [show 393 = 247 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 27 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (393 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_393 :
    recurrence4Scalar2Exceptional.coeff 393 =
      -((((255120325396263556826934106980579673547429970643049792431961 * 10 ^ 70 +
        6129980529662507346092582977840172107532568266592554713104877999697825) * 10 ^ 70 +
        7924157291561493711233629224672175051008133225079153612231354891407993) * 10 ^ 70 +
        3561613341328073587850098898754493984473001386273390284637236031102797) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (393 - x)) = _
  rw [show 394 = 248 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 26 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (394 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_394 :
    recurrence4Scalar2Exceptional.coeff 394 =
      ((((90489998240858756556432903432836921708472819654434006699180 * 10 ^ 70 +
        1379860997398132311312670711771663015722092343009790345820762819815734) * 10 ^ 70 +
        4745208845871442799298512337019619461344475871056956572274343771106501) * 10 ^ 70 +
        9783684260017199699899278535957505284416200863118564861930013035201142) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (394 - x)) = _
  rw [show 395 = 249 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 25 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (395 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_395 :
    recurrence4Scalar2Exceptional.coeff 395 =
      -((((30933240522008862683531207946674196003664079357387233520321 * 10 ^ 70 +
        4505976345214820219211749710449874972530412717096861046622809132852966) * 10 ^ 70 +
        0167026823395163877960325222288146216699844073489744086074796889155685) * 10 ^ 70 +
        6013018271397966354007922959264788714260085245147901580445540460640877) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (395 - x)) = _
  rw [show 396 = 250 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 24 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (396 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_396 :
    recurrence4Scalar2Exceptional.coeff 396 =
      ((((10161612921583645892224147471715761593143577591982166864294 * 10 ^ 70 +
        3176837985575292450456348320483762258713256075542244730979022919143511) * 10 ^ 70 +
        1114385376853671753264999496834468095699945624613753667345852022823770) * 10 ^ 70 +
        6961967420149216284451915282720516189286797569671011239875085523319838) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (396 - x)) = _
  rw [show 397 = 251 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 23 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (397 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_397 :
    recurrence4Scalar2Exceptional.coeff 397 =
      -((((3192885366813986313802598147336904453929979801765887174785 * 10 ^ 70 +
        5472793489728244499349093657184713169329913830436097756510950498795435) * 10 ^ 70 +
        0599969626298042599510638862083242584752714776398928789181576117276993) * 10 ^ 70 +
        7264228366881399842329798398787818490033845718286831012223158366608334) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (397 - x)) = _
  rw [show 398 = 252 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 22 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (398 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_398 :
    recurrence4Scalar2Exceptional.coeff 398 =
      ((((952473422660556608822935916166386149896691794169749514877 * 10 ^ 70 +
        2833986708027015410960042424460942690136835149042422744046820803668421) * 10 ^ 70 +
        5160297902154766818801526380072639849582355999917051869921620871940771) * 10 ^ 70 +
        9549526496497782913786140607107673466826436954116602758893443008169405) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (398 - x)) = _
  rw [show 399 = 253 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 21 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (399 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_399 :
    recurrence4Scalar2Exceptional.coeff 399 =
      -((((266425874167535484271074149507131908677538135181822128629 * 10 ^ 70 +
        5147207741670352574012193403057400121518453225364370934951162244362427) * 10 ^ 70 +
        0292454131711144301879912047552176986102639718801457113682532471363057) * 10 ^ 70 +
        5736554343035092224587764655477315152506030864736692499767922821687377) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (399 - x)) = _
  rw [show 400 = 254 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 20 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (400 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_400 :
    recurrence4Scalar2Exceptional.coeff 400 =
      ((((68304485842756418807805936206744458040574616161844523269 * 10 ^ 70 +
        8469825478797076775994357281791225273688081838080493343793929929111725) * 10 ^ 70 +
        8388271546226056198639028109460808737002269136642411454213575260476254) * 10 ^ 70 +
        7497795517771776871248538953021534445514826731677749877080042920886710) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (400 - x)) = _
  rw [show 401 = 255 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 19 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (401 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_401 :
    recurrence4Scalar2Exceptional.coeff 401 =
      -((((15273832741607102307051046569169622223096298540409684335 * 10 ^ 70 +
        0856055509646942856810779406367398494241692435981948568542118519625873) * 10 ^ 70 +
        3443163754285901035044282052134255918200614629849556438721308889354948) * 10 ^ 70 +
        9227701618401125055383288989335397870626968018777493334151148184766358) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (401 - x)) = _
  rw [show 402 = 256 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 18 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (402 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_402 :
    recurrence4Scalar2Exceptional.coeff 402 =
      ((((2565547937561171181632592247245124562307764111673707767 * 10 ^ 70 +
        3616288335164613266831273308377761803877932029787226430820442151013742) * 10 ^ 70 +
        1320795820053909749976141717380531611392999168463565629300398731554346) * 10 ^ 70 +
        6424579024885912906632154588711174245861795291064463351841405661707889) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (402 - x)) = _
  rw [show 403 = 257 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 17 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (403 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_403 :
    recurrence4Scalar2Exceptional.coeff 403 =
      -((((68857434420540586574852289423121079689352831616301903 * 10 ^ 70 +
        6413082533122974673482516505600858401716967456886791135364573154395252) * 10 ^ 70 +
        3863601851256389742057316736218285179144822558406154691049920425807517) * 10 ^ 70 +
        0732160810319293844226864227197488754519279081884807032281204324425703) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (403 - x)) = _
  rw [show 404 = 258 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 16 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (404 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_404 :
    recurrence4Scalar2Exceptional.coeff 404 =
      -((((201514313387523038187819383213568637280749493674180870 * 10 ^ 70 +
        7554678615335394404595679585101874597136993734619478987129640214354617) * 10 ^ 70 +
        2945595497220537250019232082971795940505835733970514578549333806264608) * 10 ^ 70 +
        7105358995541352667354776201236895870259305969705658839463431462103588) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (404 - x)) = _
  rw [show 405 = 259 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 15 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (405 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_405 :
    recurrence4Scalar2Exceptional.coeff 405 =
      ((((124702692647284355985315073831802748390642830218622337 * 10 ^ 70 +
        5621094580763171608939611905382046845143389243644233447834364568680139) * 10 ^ 70 +
        5150415104888602635354335600198655345502252220575934786821447044725659) * 10 ^ 70 +
        5984952699325720105711831391090963451755360432418779617766399211844134) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (405 - x)) = _
  rw [show 406 = 260 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 14 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (406 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_406 :
    recurrence4Scalar2Exceptional.coeff 406 =
      -((((54123837863119862991401682619652528169267297541983902 * 10 ^ 70 +
        9617086228957565578307313780011260739295443202372661938879081201939701) * 10 ^ 70 +
        7707089410021533540896693415287121689557583345948296388149621774841884) * 10 ^ 70 +
        8358333503859218491152045735009653200683901061596682221220383332569440) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (406 - x)) = _
  rw [show 407 = 261 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 13 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (407 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_407 :
    recurrence4Scalar2Exceptional.coeff 407 =
      ((((19996662371670540096277131897079738683439975418590520 * 10 ^ 70 +
        2541503488934302916562603999244989550916633495481149140158048672745297) * 10 ^ 70 +
        4764751385429489173875908374433449065065789554124919652768304878698103) * 10 ^ 70 +
        2717283773918916300192691672220750341610520310081577397069792628306908) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (407 - x)) = _
  rw [show 408 = 262 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 12 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (408 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_408 :
    recurrence4Scalar2Exceptional.coeff 408 =
      -((((6646842409273453836110590520950321602836879504671276 * 10 ^ 70 +
        3724601409862304316492545303429717806865394240107284978175372233711661) * 10 ^ 70 +
        4118062300938728444324243441225517423103040962480483126379983131436187) * 10 ^ 70 +
        9616784713787778006818399563516367532375005676067050112996972984290314) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (408 - x)) = _
  rw [show 409 = 263 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 11 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (409 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_409 :
    recurrence4Scalar2Exceptional.coeff 409 =
      ((((2030657767034710056267509129023967456556363596671428 * 10 ^ 70 +
        7978997270093525634100729454756202057966401734433236338296876481234518) * 10 ^ 70 +
        2330479561861322765132431829147612455340217615920927325588538276538681) * 10 ^ 70 +
        5209872129500413500359693396118219584500125607455571886522894513565586) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (409 - x)) = _
  rw [show 410 = 264 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 10 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (410 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_410 :
    recurrence4Scalar2Exceptional.coeff 410 =
      -((((574468355517337702132075301023574601929119351861848 * 10 ^ 70 +
        8780982888821508716781762000501209768283951167284451555776008395444969) * 10 ^ 70 +
        2302279752400731869571610452235525853505304195604198437469471657490028) * 10 ^ 70 +
        7173579099618262201950487191678869733513354927590215186978861444623199) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (410 - x)) = _
  rw [show 411 = 265 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 9 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (411 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_411 :
    recurrence4Scalar2Exceptional.coeff 411 =
      ((((150272738580388936403341545270750329723648689576794 * 10 ^ 70 +
        0248051378787034517574681339277988259447060272873787528972516458746010) * 10 ^ 70 +
        4954549610912390228619556160706369356792574919789805956348606564358925) * 10 ^ 70 +
        0898846394455645671237384166245366511253936288678783021924773347280632) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (411 - x)) = _
  rw [show 412 = 266 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 8 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (412 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_412 :
    recurrence4Scalar2Exceptional.coeff 412 =
      -((((35939072972762811730063609078087338036737631678326 * 10 ^ 70 +
        7889561690117506982151400716467362469437163920031130977638092057507751) * 10 ^ 70 +
        4341277834454564383361157330069277269504367629693863199345930981653755) * 10 ^ 70 +
        8970599037400074278067872464022587400932997116074790668874439385247623) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (412 - x)) = _
  rw [show 413 = 267 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 7 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (413 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_413 :
    recurrence4Scalar2Exceptional.coeff 413 =
      ((((7628869539731953412620573159134944157308313556304 * 10 ^ 70 +
        8917336324112652431165125045523925253956760472141058125865272614662522) * 10 ^ 70 +
        5427427713420867789317050363943471812957453981577279271793098392537439) * 10 ^ 70 +
        4312251248695448409133324197212448137401312935744415455978501506380453) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (413 - x)) = _
  rw [show 414 = 268 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 6 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (414 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_414 :
    recurrence4Scalar2Exceptional.coeff 414 =
      -((((1324134200034594566475420469952803698900918866031 * 10 ^ 70 +
        4857712503972356254648083542475941784657247245063983457619913165176883) * 10 ^ 70 +
        7280292008343504527064176578081595374853095803761012095911576262249092) * 10 ^ 70 +
        7976697125287621014587090159036811672891035981314299886962533962574070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (414 - x)) = _
  rw [show 415 = 269 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 5 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (415 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_415 :
    recurrence4Scalar2Exceptional.coeff 415 =
      ((((129547994380375934383430475294028492795688007245 * 10 ^ 70 +
        5116781431195289017120181237916215254683065535860669661041131971747795) * 10 ^ 70 +
        4642177293877702892457394520678173274906868873062147181377251499940472) * 10 ^ 70 +
        5830410123784306513442556477421730239500877108663515458846121314046336) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (415 - x)) = _
  rw [show 416 = 270 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 4 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (416 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_416 :
    recurrence4Scalar2Exceptional.coeff 416 =
      ((((28799596927581098551311335526913059123755939841 * 10 ^ 70 +
        5618737072391013067321469121404155696325785805356174792796471923173016) * 10 ^ 70 +
        1058664598809338744084960026570115453811983103803819856004800795170888) * 10 ^ 70 +
        8414980371623965504921789429212959102295465021863377505138142833801853) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (416 - x)) = _
  rw [show 417 = 271 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 3 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (417 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_417 :
    recurrence4Scalar2Exceptional.coeff 417 =
      -((((24019304639848969478980315951255748344610415115 * 10 ^ 70 +
        5303731192486937623334339123504931250044711470113764729579769114996206) * 10 ^ 70 +
        4082197826366773884386614137997331473280196335986812657590670289595010) * 10 ^ 70 +
        9084327808530880766994442878494568418494436070293763378241183360005646) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (417 - x)) = _
  rw [show 418 = 272 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 2 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (418 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_418 :
    recurrence4Scalar2Exceptional.coeff 418 =
      ((((10215663121202858636390052599130637094757346438 * 10 ^ 70 +
        8659915772196377819121472709348308308277387040589104765730001930571404) * 10 ^ 70 +
        3801502859395961254472999828103056778987802460427897179295186541866324) * 10 ^ 70 +
        9471463441093704249190341120630906624620757278757456987087774999534665) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (418 - x)) = _
  rw [show 419 = 273 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 1 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (419 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_419 :
    recurrence4Scalar2Exceptional.coeff 419 =
      -((((3502281556683445030486244889255463890966819990 * 10 ^ 70 +
        3437742582834118601330041708412869234906433071618928319697903122898744) * 10 ^ 70 +
        8010102499526970441103852783679962466108957669630807324148175083272291) * 10 ^ 70 +
        5055324430807282546103348938921402418775265583087217039310723588835111) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (419 - x)) = _
  rw [show 420 = 274 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (420 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_420 :
    recurrence4Scalar2Exceptional.coeff 420 =
      ((((1059685936958712377281105280190366387836743062 * 10 ^ 70 +
        4213639339656786849138796446219581725473010738779232811559906978337394) * 10 ^ 70 +
        9777796013123267561310944411122820912611712826236014733790965322493608) * 10 ^ 70 +
        8425295535224346116574969747505314525462404711397878204451315900490573) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (420 - x)) = _
  rw [show 421 = 275 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 31 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (421 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_421 :
    recurrence4Scalar2Exceptional.coeff 421 =
      -((((291731008339702161466731626308063472133253459 * 10 ^ 70 +
        0602517251204382276337303926002917171861367715779845975311025615837521) * 10 ^ 70 +
        8315640016042348297118983700842866448159815030218715391361948689536581) * 10 ^ 70 +
        8771476129378347006229380839804985420481866196245048988994469199436232) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (421 - x)) = _
  rw [show 422 = 276 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 30 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (422 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_422 :
    recurrence4Scalar2Exceptional.coeff 422 =
      ((((73780956442930037182890233980530343464308965 * 10 ^ 70 +
        7215872946013577414204564945734420785890599819998761139466034970792630) * 10 ^ 70 +
        2029038668320427523851323536164944962508586163346397289856533812616975) * 10 ^ 70 +
        2476864648473278716450199527289152830527594166467675702188624085030977) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (422 - x)) = _
  rw [show 423 = 277 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 29 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (423 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_423 :
    recurrence4Scalar2Exceptional.coeff 423 =
      -((((17108642796812232101131162594878865739552414 * 10 ^ 70 +
        9588755504171675162481548799658251996283523915641316786683297337445410) * 10 ^ 70 +
        8042084131477520662461887144417311839548536339829177229240964249754930) * 10 ^ 70 +
        9335339415861802338235110000103177919184614154929812368738491358127382) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (423 - x)) = _
  rw [show 424 = 278 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 28 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (424 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_424 :
    recurrence4Scalar2Exceptional.coeff 424 =
      ((((3591237517204011367018348660196944873049642 * 10 ^ 70 +
        5251677789558296350801569569312280105628354982485350313243056840836579) * 10 ^ 70 +
        0826961313374605803623779464684297426708827597898921921148499794956751) * 10 ^ 70 +
        1471292308949818080037309875501891925718904423920107111210090363430468) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (424 - x)) = _
  rw [show 425 = 279 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 27 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (425 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_425 :
    recurrence4Scalar2Exceptional.coeff 425 =
      -((((662008746318349524721839996686746058214504 * 10 ^ 70 +
        4556001665930618165211649798293198218643613222788881938434437419227756) * 10 ^ 70 +
        3721297680068514317933998735958203490202559655057276626573584763599568) * 10 ^ 70 +
        3889642650035528259432651359795685591568580797475581137834043137444300) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (425 - x)) = _
  rw [show 426 = 280 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (426 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_426 :
    recurrence4Scalar2Exceptional.coeff 426 =
      ((((99328148671512139554690490193738153117911 * 10 ^ 70 +
        0351979042338030636704728090835708039573827018450991051147644497213857) * 10 ^ 70 +
        6883550806069390387382793953457739561508270654662798962377221288851446) * 10 ^ 70 +
        3538247905406271786889467256343824813918300556249069309603379576363998) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (426 - x)) = _
  rw [show 427 = 281 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 25 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (427 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_427 :
    recurrence4Scalar2Exceptional.coeff 427 =
      -((((9019519518329607964770625204178863398550 * 10 ^ 70 +
        9743216616891496684318149706631072894225738177685711085189912975564698) * 10 ^ 70 +
        8391663326147321158745293659503886770772865006912312348729442425053532) * 10 ^ 70 +
        7841402853407462487258481700791074707044994923689252688932683371251842) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (427 - x)) = _
  rw [show 428 = 282 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 24 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (428 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_428 :
    recurrence4Scalar2Exceptional.coeff 428 =
      -((((939802673612669250765222156356687736153 * 10 ^ 70 +
        6305516929469715277031221135769078812628074730600689625717032733320819) * 10 ^ 70 +
        5066015041208365818470998227483691436436556722806952298055815891844010) * 10 ^ 70 +
        3500997750473571926016842424180278440844117577218236949822903106049056) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (428 - x)) = _
  rw [show 429 = 283 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (429 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_429 :
    recurrence4Scalar2Exceptional.coeff 429 =
      ((((748311048135036272421885064183746624400 * 10 ^ 70 +
        3016866740267970936502737671081480836333810211101418774506647250443979) * 10 ^ 70 +
        7971599386649503071546627074531485692840182605106855037415644376825685) * 10 ^ 70 +
        7292501980564599495690095049160795561153584476070059902631966448319310) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (429 - x)) = _
  rw [show 430 = 284 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 22 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (430 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_430 :
    recurrence4Scalar2Exceptional.coeff 430 =
      -((((237480025100723823788169302909421755529 * 10 ^ 70 +
        4125307435730475610883829151012001279456098845193993634602012695801409) * 10 ^ 70 +
        3613176443562163932990621418451250160410283978949430699233441016151108) * 10 ^ 70 +
        4646109268305436178210527866262047323787234252075749902492096006811558) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (430 - x)) = _
  rw [show 431 = 285 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 21 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (431 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_431 :
    recurrence4Scalar2Exceptional.coeff 431 =
      ((((55211147494965513039912065815104724817 * 10 ^ 70 +
        6735058553919496172027429407396293930098768190846941178221601114536677) * 10 ^ 70 +
        8014234611612716746921513778192879960318668089051432551197619342073192) * 10 ^ 70 +
        4756622117558228376143256933388959291143080014327264680308082617995071) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (431 - x)) = _
  rw [show 432 = 286 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 20 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (432 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_432 :
    recurrence4Scalar2Exceptional.coeff 432 =
      -((((10039927181505957620531235068635171818 * 10 ^ 70 +
        7454697471860650916156588286226150998175758585526956926306331136577535) * 10 ^ 70 +
        5661102649829089140810802645083617342543710585110350893224915012724858) * 10 ^ 70 +
        9184907998927155818009350664392992882888864336738813633623938733092709) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (432 - x)) = _
  rw [show 433 = 287 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 19 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (433 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_433 :
    recurrence4Scalar2Exceptional.coeff 433 =
      ((((1323658145261286223150180281568177645 * 10 ^ 70 +
        6475338865525184579836761835775805951569761249480814889449019044940983) * 10 ^ 70 +
        0901937366301815545689509580793914451604012188648521280539452755520679) * 10 ^ 70 +
        6685171815800409853837036639899306067143908713695963939495802297806817) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (433 - x)) = _
  rw [show 434 = 288 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 18 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (434 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_434 :
    recurrence4Scalar2Exceptional.coeff 434 =
      -((((66240619180047646000208785949538412 * 10 ^ 70 +
        3163803322894716333349818289956788973729447955997028739556136221123127) * 10 ^ 70 +
        5853538515109988732553639056757984186547125430206185805148382492883946) * 10 ^ 70 +
        2167264075970143773853977599312397078429699256687771472341753242314933) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (434 - x)) = _
  rw [show 435 = 289 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 17 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (435 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_435 :
    recurrence4Scalar2Exceptional.coeff 435 =
      -((((27661201289622204659511700536266523 * 10 ^ 70 +
        6289231482831465773667534001432615087626457494611279164675194483667021) * 10 ^ 70 +
        3471403838742016105748350953687959873962642327659190550459993049957782) * 10 ^ 70 +
        8618911864006520323204038661222730363050689539114540778191728294187332) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (435 - x)) = _
  rw [show 436 = 290 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 16 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (436 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_436 :
    recurrence4Scalar2Exceptional.coeff 436 =
      ((((11669650679969726875015556778005833 * 10 ^ 70 +
        9763754673371056134751828423773502871410202415566253551419973218127301) * 10 ^ 70 +
        6210146146120584115344666134023068415636591050414783628789608358882632) * 10 ^ 70 +
        3152366124513008041539749065602053379068821730185758134779372898368950) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (436 - x)) = _
  rw [show 437 = 291 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (437 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_437 :
    recurrence4Scalar2Exceptional.coeff 437 =
      -((((2846481246213139020116147263040332 * 10 ^ 70 +
        8964097770807154043018225478764009737295504039420878305119804001154110) * 10 ^ 70 +
        8285584534246816675525785449752111698734256693349157826740996228239588) * 10 ^ 70 +
        4853402136632183526046217453291935858709133297479092249970786092271630) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (437 - x)) = _
  rw [show 438 = 292 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 14 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (438 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_438 :
    recurrence4Scalar2Exceptional.coeff 438 =
      ((((518896115601312843514723480970962 * 10 ^ 70 +
        2319083510933624710361588184338063445194600260560138585899350980016941) * 10 ^ 70 +
        7544612143227655068759683761684088072245757092376006800452594312140483) * 10 ^ 70 +
        0718280753599521562802467559313506455143040173888582731891502054261431) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (438 - x)) = _
  rw [show 439 = 293 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 13 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (439 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_439 :
    recurrence4Scalar2Exceptional.coeff 439 =
      -((((71318285813326592014825082417068 * 10 ^ 70 +
        3843057952054983452250277012798965423499992459039017928299449051112978) * 10 ^ 70 +
        5513281954137805484606798206098890776615875592900771727877513544291462) * 10 ^ 70 +
        2075530485024433372407035698412639538455773471482604184854525825681060) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (439 - x)) = _
  rw [show 440 = 294 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 12 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (440 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_440 :
    recurrence4Scalar2Exceptional.coeff 440 =
      ((((6131268487203467831499603209850 * 10 ^ 70 +
        8791532637950186144005514706942551083243045886653460178762072047735958) * 10 ^ 70 +
        3734000190040303687458780169445358056306530035998657562514383675548604) * 10 ^ 70 +
        7495432025431717161656603755922959955178874646311869197541880308772999) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (440 - x)) = _
  rw [show 441 = 295 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 11 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (441 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_441 :
    recurrence4Scalar2Exceptional.coeff 441 =
      ((((169248700921809684812558998643 * 10 ^ 70 +
        7812907609986224171849898367455763621204599436505654420093134208720816) * 10 ^ 70 +
        4775020840144991109325198354923457443185909258195194912916747594251418) * 10 ^ 70 +
        9160409353222856764713756255943285901045460194432763539596675702665255) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (441 - x)) = _
  rw [show 442 = 296 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 10 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (442 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_442 :
    recurrence4Scalar2Exceptional.coeff 442 =
      -((((197930421971802113506766206942 * 10 ^ 70 +
        9549981364920782491507886224181166367715684019710288749459178181351578) * 10 ^ 70 +
        3733719809572368221691157538679325897837832330585934542376206693949099) * 10 ^ 70 +
        1268921663506192898503747159559097803379068649902639491967508416560444) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (442 - x)) = _
  rw [show 443 = 297 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 9 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (443 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_443 :
    recurrence4Scalar2Exceptional.coeff 443 =
      ((((47375862736804867864545459335 * 10 ^ 70 +
        0050393817623606611404583672518591429610095587292606375818748228737854) * 10 ^ 70 +
        4028296060224368695610426335786031341369127581257313835346107557326566) * 10 ^ 70 +
        4445678786162185941455498208564004663913235238027572441385760513012423) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (443 - x)) = _
  rw [show 444 = 298 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 8 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (444 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_444 :
    recurrence4Scalar2Exceptional.coeff 444 =
      -((((7480159186353506251803909938 * 10 ^ 70 +
        3801116315073014615289350490145340838386900495545441414804287611871993) * 10 ^ 70 +
        4843933600629037208072981563547771676855946339977603114346581338181414) * 10 ^ 70 +
        2178935633934781253023824141700343774030789829765474508587390929720576) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (444 - x)) = _
  rw [show 445 = 299 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 7 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (445 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_445 :
    recurrence4Scalar2Exceptional.coeff 445 =
      ((((820303733276522037035650670 * 10 ^ 70 +
        8214892119386217640936119127843410348758856972550892095678315756465327) * 10 ^ 70 +
        9402498093823920129063902834112060400696309838424428037325665377025500) * 10 ^ 70 +
        7934479616432387373622745908533230113957814353820103996738805067800479) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (445 - x)) = _
  rw [show 446 = 300 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 6 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (446 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_446 :
    recurrence4Scalar2Exceptional.coeff 446 =
      -((((45138559845705614874829795 * 10 ^ 70 +
        4566209459029576655294960337986110481921407261931453694996201290734613) * 10 ^ 70 +
        2020509772101868217507814660211927473977955107064101496218607264296519) * 10 ^ 70 +
        3065124303302217355564523568246316241216323103497938734807842989324610) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (446 - x)) = _
  rw [show 447 = 301 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 5 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (447 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_447 :
    recurrence4Scalar2Exceptional.coeff 447 =
      -((((4726264808572217054317550 * 10 ^ 70 +
        6507808748556783584910546621468110306381883660595001796601600050960808) * 10 ^ 70 +
        1766795141817151906259093452422273379271501992703956192574277725881950) * 10 ^ 70 +
        0309053713354793819020969808642803261122724558210331103804786135962291) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (447 - x)) = _
  rw [show 448 = 302 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 4 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (448 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_448 :
    recurrence4Scalar2Exceptional.coeff 448 =
      ((((1745658078472760416988151 * 10 ^ 70 +
        1580339921964880179321454693592760329893066142952752128595508763638642) * 10 ^ 70 +
        7448072645955786261318699944237720458540010841102541190098582671849192) * 10 ^ 70 +
        1518740982910287132674794816687256754885549634394941624313579182338070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (448 - x)) = _
  rw [show 449 = 303 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 3 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (449 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_449 :
    recurrence4Scalar2Exceptional.coeff 449 =
      -((((277927398161374379442868 * 10 ^ 70 +
        3824519569121388993614336525534427281626817006669683594794706637145869) * 10 ^ 70 +
        5610090072503033540093841930365750251807590183404255435128364821970300) * 10 ^ 70 +
        0629099340117392767206779709506025603790809954877103317535561174181860) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (449 - x)) = _
  rw [show 450 = 304 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 2 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (450 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_450 :
    recurrence4Scalar2Exceptional.coeff 450 =
      ((((28314147841209632009102 * 10 ^ 70 +
        1986520005985919458389779400292650625368168031705825365078808030466761) * 10 ^ 70 +
        4329173552996007995696733831313683421961149035851312305423497469938316) * 10 ^ 70 +
        1785724174495463489016217897543200654798357250465753920911266328187533) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (450 - x)) = _
  rw [show 451 = 305 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 1 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (451 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_451 :
    recurrence4Scalar2Exceptional.coeff 451 =
      -((((1503893266684341152797 * 10 ^ 70 +
        7756642597658637568331951676769236636916266656245237623634120124446719) * 10 ^ 70 +
        1385925518049440196763348721567357577226549263541121207325559971967828) * 10 ^ 70 +
        5449999450598550675043979451510049753939509168820184596410819263062984) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (451 - x)) = _
  rw [show 452 = 306 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (452 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_452 :
    recurrence4Scalar2Exceptional.coeff 452 =
      -((((79987386467794273986 * 10 ^ 70 +
        9228989459270151050969457563342986813705442859085166981030401824198803) * 10 ^ 70 +
        9281436895131984449616267086502000332097588192296009663519532178117390) * 10 ^ 70 +
        6240193243223786689631403354545705372892615224376977523126065756906672) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (452 - x)) = _
  rw [show 453 = 307 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 31 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (453 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_453 :
    recurrence4Scalar2Exceptional.coeff 453 =
      ((((28998575763742349467 * 10 ^ 70 +
        5454518338758035995498718878471001551319418157792680348359711224678874) * 10 ^ 70 +
        6481125331257749125574690671829708783173369471623710133274916078511901) * 10 ^ 70 +
        0525139626161116994131723766740686064471898930147774647451260459338134) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (453 - x)) = _
  rw [show 454 = 308 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 30 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (454 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_454 :
    recurrence4Scalar2Exceptional.coeff 454 =
      -((((3525556380850161672 * 10 ^ 70 +
        3290779860621765997623750397928250621854773181244206713421131757707371) * 10 ^ 70 +
        1941817723857909484720550562409128168396446779833541446959829523067669) * 10 ^ 70 +
        8860892041607004916061208460918513439500609824278389318287383921874420) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (454 - x)) = _
  rw [show 455 = 309 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 29 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (455 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_455 :
    recurrence4Scalar2Exceptional.coeff 455 =
      ((((226222901950331308 * 10 ^ 70 +
        0504881497110376623410675767711812283890645173099636298545552709132464) * 10 ^ 70 +
        8904711249472637312504075375594638064285107595101428431037842690676289) * 10 ^ 70 +
        6476493441207322881515230921112877710589762945924135217758162785579710) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (455 - x)) = _
  rw [show 456 = 310 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 28 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (456 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_456 :
    recurrence4Scalar2Exceptional.coeff 456 =
      ((((327850011368492 * 10 ^ 70 +
        3214708735166239439376688244869163620710259711080758292784688826775118) * 10 ^ 70 +
        6199632980959288119724807474323110142677660053645028296271154080086858) * 10 ^ 70 +
        0609133368500748539497271935097930542076442875364062520587565379470048) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (456 - x)) = _
  rw [show 457 = 311 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 27 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (457 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_457 :
    recurrence4Scalar2Exceptional.coeff 457 =
      -((((1822116922485952 * 10 ^ 70 +
        6094146544057355066154532704003051840911074380005966874188450712741766) * 10 ^ 70 +
        6629650549964847927725196610784524999779631542226795791422304667596397) * 10 ^ 70 +
        7136129290637353823569592093817491901585104899254697027685732218600296) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (457 - x)) = _
  rw [show 458 = 312 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 26 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (458 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_458 :
    recurrence4Scalar2Exceptional.coeff 458 =
      ((((207661258754602 * 10 ^ 70 +
        3608529380733579572353351288677095652189661186108686184047608645342812) * 10 ^ 70 +
        9280902972773687257767091446925049029382802357698370564778758687573457) * 10 ^ 70 +
        4406057820951617762829654712054090311183009357451591283135406223639786) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (458 - x)) = _
  rw [show 459 = 313 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 25 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (459 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_459 :
    recurrence4Scalar2Exceptional.coeff 459 =
      -((((10185856443297 * 10 ^ 70 +
        0540225376720431785209683061511245951459232267658810029812479507544505) * 10 ^ 70 +
        1418349735469317738412938385229805456158672998403974934371913443706241) * 10 ^ 70 +
        1545526449216713480187675666311387876524706313435594617139701148751933) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (459 - x)) = _
  rw [show 460 = 314 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 24 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (460 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_460 :
    recurrence4Scalar2Exceptional.coeff 460 =
      -((((245775244042 * 10 ^ 70 +
        4902866114629863100942581979297102883456811151242665213969797191540326) * 10 ^ 70 +
        6040003996272766685561394818981938962589082843582266336159444582075848) * 10 ^ 70 +
        1652793928701049734795569365449674211023736026438108523040476072313941) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (460 - x)) = _
  rw [show 461 = 315 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 23 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (461 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_461 :
    recurrence4Scalar2Exceptional.coeff 461 =
      ((((78525433744 * 10 ^ 70 +
        2797099274761919153299151141155902872508648430896470843413227382899186) * 10 ^ 70 +
        9672439299569614569293939951388841562073058704597999753373554391767861) * 10 ^ 70 +
        0036648544638008428373068087211533647219707379088789470926973100430166) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (461 - x)) = _
  rw [show 462 = 316 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 22 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (462 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_462 :
    recurrence4Scalar2Exceptional.coeff 462 =
      -((((5330232239 * 10 ^ 70 +
        8240958435327624862305384742522446656365637817047131462915095017833458) * 10 ^ 70 +
        9373673172258077690181126448874278677511520094854179179740342016567837) * 10 ^ 70 +
        1672564354387674900439825891495240226506784278887859221121016206063319) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (462 - x)) = _
  rw [show 463 = 317 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 21 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (463 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_463 :
    recurrence4Scalar2Exceptional.coeff 463 =
      ((((49465417 * 10 ^ 70 +
        6114300721682894662184382041551866257826833722719311756661340379729292) * 10 ^ 70 +
        5437563410286367575620154300868287770659172341167247742526069597210897) * 10 ^ 70 +
        4522237171169652887186820654662467009189447506440943323334293399606003) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (463 - x)) = _
  rw [show 464 = 318 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 20 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (464 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_464 :
    recurrence4Scalar2Exceptional.coeff 464 =
      ((((18292182 * 10 ^ 70 +
        8919533653261341416639736650222721516671488694380069982278068554461832) * 10 ^ 70 +
        4450657458795168175273153917305976543335563691797576985628007938323426) * 10 ^ 70 +
        5056336407327484932778054592278003187425751655838738866581171343918571) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (464 - x)) = _
  rw [show 465 = 319 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 19 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (465 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_465 :
    recurrence4Scalar2Exceptional.coeff 465 =
      -((((1284827 * 10 ^ 70 +
        0088772861625531441457826102792519203886745488665361363784890291384261) * 10 ^ 70 +
        0087254194874983680627998119824594871797809331273577014852666059913431) * 10 ^ 70 +
        8251248997287653936846132955542482106569864022389636391178734881038534) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (465 - x)) = _
  rw [show 466 = 320 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 18 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (466 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_466 :
    recurrence4Scalar2Exceptional.coeff 466 =
      ((((7909 * 10 ^ 70 +
        9414001053601790431797020415427813554521721457516702662787342633959628) * 10 ^ 70 +
        8134114592200292632826889872980318993609064330893730281081757128965023) * 10 ^ 70 +
        3895962680853947984442584354906302518862105894275138379896804222131392) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (466 - x)) = _
  rw [show 467 = 321 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 17 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (467 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_467 :
    recurrence4Scalar2Exceptional.coeff 467 =
      ((((3427 * 10 ^ 70 +
        8496199788387046442798404762091456827008439695433833419284758628214328) * 10 ^ 70 +
        4179919576367944796362070195640420687211277909544348263666898045768806) * 10 ^ 70 +
        7334494272130484971190832447158637595772180282191489963609971688878889) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (467 - x)) = _
  rw [show 468 = 322 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 16 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (468 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_468 :
    recurrence4Scalar2Exceptional.coeff 468 =
      -((((153 * 10 ^ 70 +
        6697955462629679405096121708933084344513101891826001628487963786950881) * 10 ^ 70 +
        4397825021281584344012809214819930114178285350252496752858117610699214) * 10 ^ 70 +
        5657518471831012692923803432445667527542213480132970995791060827976100) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (468 - x)) = _
  rw [show 469 = 323 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 15 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (469 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_469 :
    recurrence4Scalar2Exceptional.coeff 469 =
      -((((3 * 10 ^ 70 +
        1817512410528153078502826649983210257921354798107368213145092129804653) * 10 ^ 70 +
        7959628248044464937830383933846539387555534336350547512147267765574505) * 10 ^ 70 +
        9658262227577521273500513034707036518617304107007127004900904570197561) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (469 - x)) = _
  rw [show 470 = 324 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 14 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (470 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_470 :
    recurrence4Scalar2Exceptional.coeff 470 =
      (((4025489490301918115825219485964795218710608336363189039081378408022519 * 10 ^ 70 +
        2343449862917462361133992029523611392526999298063604751295398184448406) * 10 ^ 70 +
        0108499904340520308290004082084418811918856936002029163545666012092745) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (470 - x)) = _
  rw [show 471 = 325 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 13 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (471 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_471 :
    recurrence4Scalar2Exceptional.coeff 471 =
      -(((15508506311584031816191079042181862986175366934506812925375481825585 * 10 ^ 70 +
        9635969278717583036539664457089308120710538349574214770366493530676387) * 10 ^ 70 +
        1569399834575431786282044667228361022880963785572023404958492823062157) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (471 - x)) = _
  rw [show 472 = 326 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 12 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (472 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_472 :
    recurrence4Scalar2Exceptional.coeff 472 =
      -(((6468078761512087065022703221211071198252802778782862663179047758978 * 10 ^ 70 +
        7806525976422269827685840469607263436140601042113947669962043441713023) * 10 ^ 70 +
        3082106721074153554054756231613210967350081189783874414792878377205693) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (472 - x)) = _
  rw [show 473 = 327 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 11 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (473 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_473 :
    recurrence4Scalar2Exceptional.coeff 473 =
      (((61543466727160600901701403309587693721663329298797010745003277730 * 10 ^ 70 +
        3005625715002612524597531947030331661926773018648657879519638487832850) * 10 ^ 70 +
        4233569296699372158497447158824906997089473316386657273945677739029668) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (473 - x)) = _
  rw [show 474 = 328 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 10 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (474 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_474 :
    recurrence4Scalar2Exceptional.coeff 474 =
      (((8352686958553728343342389171256586309028268361675078991126803128 * 10 ^ 70 +
        9045713211187336021313591845919950631878867043706278440678882653422953) * 10 ^ 70 +
        0600164881665518167820744078185710382744262089219280063220706434718299) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (474 - x)) = _
  rw [show 475 = 329 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 9 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (475 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_475 :
    recurrence4Scalar2Exceptional.coeff 475 =
      -(((20678855757293616866852354390543791035133089625572757985362963 * 10 ^ 70 +
        2694387928780178629261375695153016019029603261394431761345281511539704) * 10 ^ 70 +
        7794334307692779518425839653097890166170886734297380408545833544993451) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (475 - x)) = _
  rw [show 476 = 330 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 8 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (476 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_476 :
    recurrence4Scalar2Exceptional.coeff 476 =
      -(((8585936751464978812380320992072260611611769023368963143438959 * 10 ^ 70 +
        9813776644095482575972050232074529057282160818637927638241677099044096) * 10 ^ 70 +
        2282567393300060135556309603251899527694833387771293238248175152925217) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (476 - x)) = _
  rw [show 477 = 331 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 7 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (477 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_477 :
    recurrence4Scalar2Exceptional.coeff 477 =
      -(((128639210343539312072766969737085673796948363831216762779096 * 10 ^ 70 +
        6134279271709917202498230347253483620618782710592044572432564069502635) * 10 ^ 70 +
        9110389749934442847372783702706390145506229465273522019409520873720939) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (477 - x)) = _
  rw [show 478 = 332 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 6 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (478 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_478 :
    recurrence4Scalar2Exceptional.coeff 478 =
      (((3700104007976587403162289332514175894414601199828615895649 * 10 ^ 70 +
        7664168226947464425104604683024126145448951992886451121442792079772025) * 10 ^ 70 +
        7980069573165569996536042781680063399307449247148179148248960622421524) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (478 - x)) = _
  rw [show 479 = 333 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 5 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (479 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_479 :
    recurrence4Scalar2Exceptional.coeff 479 =
      (((187795939698423271368133467800132167984175340348209797902 * 10 ^ 70 +
        8620208060561975298100660811225124238622971521671744320475539691836181) * 10 ^ 70 +
        5250933974722235598473510900110269418390521581264627128001507147811236) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (479 - x)) = _
  rw [show 480 = 334 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 4 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_479_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (480 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_480 :
    recurrence4Scalar2Exceptional.coeff 480 =
      (((3940952815331820245159083216226140733306885791246516143 * 10 ^ 70 +
        3920172913250871242919656934540610547201869283386463910377431983738256) * 10 ^ 70 +
        9945013056318272905930159399172943663545144672757476106921908978705947) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (480 - x)) = _
  rw [show 481 = 335 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 3 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_480_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (481 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_481 :
    recurrence4Scalar2Exceptional.coeff 481 =
      (((52205562230586854348993749165377108583621494053663439 * 10 ^ 70 +
        8156881604145512177727156516612444520313618010956273805489645427961470) * 10 ^ 70 +
        1038920531479687119255042922201359051560891166776925737254014860179042) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (481 - x)) = _
  rw [show 482 = 336 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 2 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_481_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (482 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_482 :
    recurrence4Scalar2Exceptional.coeff 482 =
      (((482274361289914300270959672796185300704893084172091 * 10 ^ 70 +
        8790288873594275456881593022708492145357734855070159185021090037817704) * 10 ^ 70 +
        1010175001583247430480998184148609869941029625212655593934253739997747) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (482 - x)) = _
  rw [show 483 = 337 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 1 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_482_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (483 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_483 :
    recurrence4Scalar2Exceptional.coeff 483 =
      (((3205502472787648406817642472868867605917416852513 * 10 ^ 70 +
        1255952950855199585764971697166836499346762039400909149779918812676117) * 10 ^ 70 +
        2999579360534726339004465339246118846240726367701827049914044220303316) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (483 - x)) = _
  rw [show 484 = 338 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_483_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (484 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_484 :
    recurrence4Scalar2Exceptional.coeff 484 =
      (((15229717517413733342166038789464879419730321887 * 10 ^ 70 +
        2303180700679467332005337112860903491484212730199164236149112465055462) * 10 ^ 70 +
        0783838847610022727753572176148874284983016523442584458136358515717279) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (484 - x)) = _
  rw [show 485 = 339 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 31 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_484_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (485 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_485 :
    recurrence4Scalar2Exceptional.coeff 485 =
      (((48717797521415440783411879190641751043170778 * 10 ^ 70 +
        9262849393540865772854067258252185716369404775625903617858043722138358) * 10 ^ 70 +
        0960342220793856481409364708410118452290314400351681843431318306393391) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (485 - x)) = _
  rw [show 486 = 340 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 30 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_485_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (486 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_486 :
    recurrence4Scalar2Exceptional.coeff 486 =
      (((81015681900430381409152198222791822300668 * 10 ^ 70 +
        1391125331924889528158734268832486652449775751937734217399803810819907) * 10 ^ 70 +
        7390289218057278706023592673066363776874933414380256387574905153324759) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (486 - x)) = _
  rw [show 487 = 341 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 29 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_486_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (487 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_487 :
    recurrence4Scalar2Exceptional.coeff 487 =
      -(((83486965873656452391848860488288239837 * 10 ^ 70 +
        7937243828257480572498676013340203485543183914091128780008101144994519) * 10 ^ 70 +
        2509266986387132742521634759822153308762305941886764952438475103873584) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (487 - x)) = _
  rw [show 488 = 342 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 28 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_487_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (488 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_488 :
    recurrence4Scalar2Exceptional.coeff 488 =
      -(((895234397739870999879757038425953777 * 10 ^ 70 +
        7909535175289065931360376386760481415837374401660317896520979948641188) * 10 ^ 70 +
        5901954198780199959409492139506000743361303289247719272827115040052681) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (488 - x)) = _
  rw [show 489 = 343 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 27 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_488_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (489 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_489 :
    recurrence4Scalar2Exceptional.coeff 489 =
      -(((2353375725216896066535339898822551 * 10 ^ 70 +
        5751173060130620272044950762126380422876020973394367532150033193468545) * 10 ^ 70 +
        5932182292946389625588615068959617067828243444875407916819788683132106) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (489 - x)) = _
  rw [show 490 = 344 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 26 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_489_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (490 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_490 :
    recurrence4Scalar2Exceptional.coeff 490 =
      -(((2158204655384406585968350924644 * 10 ^ 70 +
        5330166034663474191735012138751761526458091275132687999509221602330906) * 10 ^ 70 +
        7797283180350414201687258300385493052561839895138144613305853128701634) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (490 - x)) = _
  rw [show 491 = 345 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 25 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_490_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (491 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_491 :
    recurrence4Scalar2Exceptional.coeff 491 =
      (((4155988359667983651302624229 * 10 ^ 70 +
        9327801884298354641342784138451854695144295897426127699000315603485105) * 10 ^ 70 +
        8457411957122135617760269164201305206041483143210754271058517969458625) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (491 - x)) = _
  rw [show 492 = 346 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 24 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_491_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (492 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_492 :
    recurrence4Scalar2Exceptional.coeff 492 =
      (((16122313938381690012051114 * 10 ^ 70 +
        7799950801803917176293952061406721586666394660627223185821497973433434) * 10 ^ 70 +
        3302824501911069784986134074786493083845367389402222303422562721407767) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (492 - x)) = _
  rw [show 493 = 347 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 23 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_492_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (493 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_493 :
    recurrence4Scalar2Exceptional.coeff 493 =
      (((20679462089242362071853 * 10 ^ 70 +
        2237749373569195876203406275226677395447560495796236956925570837183743) * 10 ^ 70 +
        0658052944348515576683890959253518488619840070605046319167649944059436) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (493 - x)) = _
  rw [show 494 = 348 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 22 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_493_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (494 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_494 :
    recurrence4Scalar2Exceptional.coeff 494 =
      (((3003192581880532401 * 10 ^ 70 +
        4360647949462903116683503286030461690190245707552904434322994611528966) * 10 ^ 70 +
        9244577705606871405975678092096749009848719461448885337546534421662012) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (494 - x)) = _
  rw [show 495 = 349 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 21 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_494_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (495 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_495 :
    recurrence4Scalar2Exceptional.coeff 495 =
      -(((29219318098292994 * 10 ^ 70 +
        9179459753321804663727488103467728967089149247883586248553202708675855) * 10 ^ 70 +
        7685389136821775341892588196349268481131875646706339841860524557348227) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (495 - x)) = _
  rw [show 496 = 350 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 20 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_495_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (496 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_496 :
    recurrence4Scalar2Exceptional.coeff 496 =
      -(((48431306376437 * 10 ^ 70 +
        2283769290573312152668479785546733720000127347561927948426983843218091) * 10 ^ 70 +
        1092067608987915176577828771211707783839254153332594583940364926006716) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (496 - x)) = _
  rw [show 497 = 351 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 19 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_496_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (497 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_497 :
    recurrence4Scalar2Exceptional.coeff 497 =
      -(((41406852700 * 10 ^ 70 +
        7241017889814287103774173346528444627671859666299124785780666173538285) * 10 ^ 70 +
        3238736330354254586777545749954306947221995301507089641117893088935700) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (497 - x)) = _
  rw [show 498 = 352 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 18 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_497_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (498 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_498 :
    recurrence4Scalar2Exceptional.coeff 498 =
      -(((22049789 * 10 ^ 70 +
        7134523172812476720251767135305799904998334709268414952991047087384993) * 10 ^ 70 +
        4252205652643652074330086297922120741095783282180521970933866498755932) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (498 - x)) = _
  rw [show 499 = 353 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 17 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_498_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (499 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_499 :
    recurrence4Scalar2Exceptional.coeff 499 =
      -(((7635 * 10 ^ 70 +
        8516995789679819980715514692341580812293876142135128038364709210703216) * 10 ^ 70 +
        8625749437456804252331162242010824284765882892518849306421363516407942) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (499 - x)) = _
  rw [show 500 = 354 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 16 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_499_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (500 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_500 :
    recurrence4Scalar2Exceptional.coeff 500 =
      -(((1 * 10 ^ 70 +
        7311927657638091806818494925863663915155193099909672026660627333181818) * 10 ^ 70 +
        1730128324005727888879697912067281746217127654743920334127339565982672) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (500 - x)) = _
  rw [show 501 = 355 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 15 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_500_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (501 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_501 :
    recurrence4Scalar2Exceptional.coeff 501 =
      -((2547575562973483269854063268819670455043806199886436714623584221685 * 10 ^ 70 +
        5611960015918314511381012211893756178984962954872819148354700639196198) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (501 - x)) = _
  rw [show 502 = 356 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 14 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_501_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 357,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (502 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_502 :
    recurrence4Scalar2Exceptional.coeff 502 =
      -((239039636525752956814950955449619776703455351773247987839363784 * 10 ^ 70 +
        6577467902512553560227785583556241546857343224048882520706369841665656) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (502 - x)) = _
  rw [show 503 = 357 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 13 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_502_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 358,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (503 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_503 :
    recurrence4Scalar2Exceptional.coeff 503 =
      -((13948249938802240823789802690710724469862692616781879775832 * 10 ^ 70 +
        6315981040083865937379362546911224886707650459846415162353144480023696) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (503 - x)) = _
  rw [show 504 = 358 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 12 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_503_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 359,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (504 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_504 :
    recurrence4Scalar2Exceptional.coeff 504 =
      -((491205909133784099876717764838648659050237784973283512 * 10 ^ 70 +
        0951109060622897635564740062507891354582163252664740619823239343254640) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (504 - x)) = _
  rw [show 505 = 359 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 11 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_504_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 360,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (505 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_505 :
    recurrence4Scalar2Exceptional.coeff 505 =
      -((10156209983676335293191339120868784072970031295017 * 10 ^ 70 +
        1140303748912650417898970852008446531463567884939903995214317013351033) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (505 - x)) = _
  rw [show 506 = 360 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 10 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_505_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 361,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (506 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_506 :
    recurrence4Scalar2Exceptional.coeff 506 =
      -((117982370022623698058226463122888927663067836 * 10 ^ 70 +
        7810044808561737680640290000986836329418694648091502541776206329062003) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (506 - x)) = _
  rw [show 507 = 361 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 9 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_506_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 362,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (507 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (507 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_507 :
    recurrence4Scalar2Exceptional.coeff 507 =
      -((719840172583233609660549940119554138033 * 10 ^ 70 +
        5984716672167844580940126578627406442033105250780833449292717146451804) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (507 - x)) = _
  rw [show 508 = 362 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 8 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_507_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 363,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (508 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Exceptional_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4ExceptionalProduct.coeff (370 + x) *
        remainder6Coefficient2.coeff (508 - (370 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4ExceptionalProduct_coeff_high (370 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_508 :
    recurrence4Scalar2Exceptional.coeff 508 =
      -((2231533975049811042106771452679688 * 10 ^ 70 +
        8565927105164372549662364511961454959501078854358331065549703947397611) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (508 - x)) = _
  rw [show 509 = 363 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 7 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Exceptional_coeff_508_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
