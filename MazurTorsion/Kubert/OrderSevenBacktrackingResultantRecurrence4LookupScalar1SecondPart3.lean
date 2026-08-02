/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
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
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163

attribute [local simp]
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_170
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
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
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91

attribute [local simp]
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar1Second_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (383 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (383 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_383 :
    recurrence4Scalar1Second.coeff 383 =
      ((((19847997079458137112362613145985584889284831870503300597215123010 * 10 ^ 70 +
        7674578479234647359227502717837451423666787343556397049578065087694363) * 10 ^ 70 +
        0066288857811920380220155517271526727977995967272436684733761948767450) * 10 ^ 70 +
        8094895066372721998862952165983669282442868677005860022739552866690364) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (383 - x)) = _
  rw [show 384 = 37 +
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
    rw [show 219 = 8 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (384 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (384 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_384 :
    recurrence4Scalar1Second.coeff 384 =
      -((((3995962610092808463593283990204952855038021438405395167368859483 * 10 ^ 70 +
        7390922739538212015480952181197792568819595198292194168803383929988029) * 10 ^ 70 +
        1114882740194285190445165249510199711890426846904686205693077381357873) * 10 ^ 70 +
        3516870902581926097137132488906103347414156751264850805072102869167366) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (384 - x)) = _
  rw [show 385 = 38 +
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
    rw [show 219 = 7 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (385 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (385 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_385 :
    recurrence4Scalar1Second.coeff 385 =
      ((((333829206123139461201096003841788257860012104317897148778527324 * 10 ^ 70 +
        4995906998932151905625597520827042232992741133964137551151916479417454) * 10 ^ 70 +
        6205658039780137013059243942485211984279953958408601571912687321419967) * 10 ^ 70 +
        1574765057680446253668418001156349435231972627849495171573266700052539) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (385 - x)) = _
  rw [show 386 = 39 +
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
    rw [show 219 = 6 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (386 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (386 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_386 :
    recurrence4Scalar1Second.coeff 386 =
      ((((233909018715489684760131896712724524951302363352269704726076340 * 10 ^ 70 +
        3357723895335855265765809054314522605308140398305514795488519088921224) * 10 ^ 70 +
        8694921010235015486130778740463558355806158385756145521180438143915607) * 10 ^ 70 +
        7799882282111894207584360509753623040567635171640498800043409183641304) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (386 - x)) = _
  rw [show 387 = 40 +
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
    rw [show 219 = 5 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (387 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (387 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_387 :
    recurrence4Scalar1Second.coeff 387 =
      -((((187028619234973139838185764947160406522932888656823793141069490 * 10 ^ 70 +
        1894920622734325440817577383248724122328960122512494606623069088069604) * 10 ^ 70 +
        8110942326595524203204536022221749214768680517621716131215159000801724) * 10 ^ 70 +
        1546030348857198949893860858532409341758413963347189430337384947700770) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (387 - x)) = _
  rw [show 388 = 41 +
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
    rw [show 219 = 4 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (388 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (388 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_388 :
    recurrence4Scalar1Second.coeff 388 =
      ((((93722143314824885170182361647393151412561957329110184204954459 * 10 ^ 70 +
        3896578782821699714360862867650614343374138661179486415624570762681453) * 10 ^ 70 +
        9955863807051857464227221142302665979545761078748434238359967207927325) * 10 ^ 70 +
        6039612112764754117343555445145348198998916212703526074145194034739770) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (388 - x)) = _
  rw [show 389 = 42 +
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
    rw [show 219 = 3 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (389 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (389 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_389 :
    recurrence4Scalar1Second.coeff 389 =
      -((((39383129011316837984666641895454088528014395544412061247407422 * 10 ^ 70 +
        8289223231687153984762684789181987452373575127951537416995387841877570) * 10 ^ 70 +
        1146101859547705009206464834271187735354869041088531864081703670732006) * 10 ^ 70 +
        0250129574363868869735816156393780135138875226757487854811108358129386) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (389 - x)) = _
  rw [show 390 = 43 +
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
    rw [show 219 = 2 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (390 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (390 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_390 :
    recurrence4Scalar1Second.coeff 390 =
      ((((15013587977511855660358581024317062085188540090699288649716241 * 10 ^ 70 +
        4307494244732673222996947139030919472877536572981615951801150899349757) * 10 ^ 70 +
        5936557672265096222604309567783559412103054653141493826677807905572102) * 10 ^ 70 +
        9242246451194382849410798834335202190361611376409957445909030944343628) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (390 - x)) = _
  rw [show 391 = 44 +
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
    rw [show 219 = 1 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (391 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (391 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_391 :
    recurrence4Scalar1Second.coeff 391 =
      -((((5402357480711864504651883900657947338150336275077249556222445 * 10 ^ 70 +
        4143267448331046533884237888873514745236460179023021372875232142467328) * 10 ^ 70 +
        2403320247667944644369840996346545410144618689427674460736546526991891) * 10 ^ 70 +
        8885551955184298435393006267757100780763189270047941119251490231249965) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (391 - x)) = _
  rw [show 392 = 45 +
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
  rw [recurrence4Scalar1Second_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (392 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (392 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_392 :
    recurrence4Scalar1Second.coeff 392 =
      ((((1891651637659851438716257804754180410197223798682921418141791 * 10 ^ 70 +
        3699422384189865986540860797992799173988750206198087063954828343649045) * 10 ^ 70 +
        0540060132409750285108353654708663713485509774227294643817627112347496) * 10 ^ 70 +
        9465921118728531367968215110589161073188091028587962883541153809585037) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (392 - x)) = _
  rw [show 393 = 46 +
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
    rw [show 251 = 31 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (393 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (393 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_393 :
    recurrence4Scalar1Second.coeff 393 =
      -((((663297251957973702932772352739313832132185253339629281040659 * 10 ^ 70 +
        4941268602195796118395828622263669659187581995857311690803651283163010) * 10 ^ 70 +
        5835503304043313638479974888596127064453944189495646351198956717646921) * 10 ^ 70 +
        7203747559576417580761925402824121138329373297856099456638108396436137) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (393 - x)) = _
  rw [show 394 = 47 +
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
    rw [show 251 = 30 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (394 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (394 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_394 :
    recurrence4Scalar1Second.coeff 394 =
      ((((238659125830610029363095063355251430380752849233066809644793 * 10 ^ 70 +
        0540712630000596074600562165185758783547131902825850831535799267626423) * 10 ^ 70 +
        2613099666223404278755190664703043170279606458098135761685355397755161) * 10 ^ 70 +
        8387242388097987309156914696345651254291773375941827060807700394763594) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (394 - x)) = _
  rw [show 395 = 48 +
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
    rw [show 251 = 29 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (395 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (395 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_395 :
    recurrence4Scalar1Second.coeff 395 =
      -((((89196962189962138040931118598776936517249145910852128843627 * 10 ^ 70 +
        0730371469183039669613397774347330631907799684469811475832991419183114) * 10 ^ 70 +
        5788660887051930535219372284781421149703437450590619554822224243728329) * 10 ^ 70 +
        7143138832982847337156314134752965920568017769812429193854920009816392) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (395 - x)) = _
  rw [show 396 = 49 +
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
    rw [show 251 = 28 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (396 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (396 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_396 :
    recurrence4Scalar1Second.coeff 396 =
      ((((34457022429602231653663491236279577884947884248939305520199 * 10 ^ 70 +
        9056490584289134172522367565173568776645024818846764943431388060231294) * 10 ^ 70 +
        7739238966826980687699760060454129360281856692849598895565536484682355) * 10 ^ 70 +
        5574340749931068017851957726422154038636358396244415716630149252632555) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (396 - x)) = _
  rw [show 397 = 50 +
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
    rw [show 251 = 27 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (397 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (397 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_397 :
    recurrence4Scalar1Second.coeff 397 =
      -((((13517589228619894490584205179254736474411555059863210072850 * 10 ^ 70 +
        7568448391532263086646992909079451628481409457073917207406829705116796) * 10 ^ 70 +
        1245975236485444337763942359405274578631497054163713618260090393967092) * 10 ^ 70 +
        1297347743026727175449021819656025875300425582915790743804802801945593) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (397 - x)) = _
  rw [show 398 = 51 +
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
    rw [show 251 = 26 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (398 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (398 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_398 :
    recurrence4Scalar1Second.coeff 398 =
      ((((5274990483650750710165039858427450314321190446463257452798 * 10 ^ 70 +
        4979038888406270225633787686022367921432137715645594451180072405237903) * 10 ^ 70 +
        9336627054749460639366258145961366066252174828809215087931519248231482) * 10 ^ 70 +
        7730967900735182553925431682623054760660221888003071566036987680391587) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (398 - x)) = _
  rw [show 399 = 52 +
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
    rw [show 251 = 25 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (399 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (399 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_399 :
    recurrence4Scalar1Second.coeff 399 =
      -((((2013199783726136128000695364221340189716973684690305450615 * 10 ^ 70 +
        7764240306379745183536920857929661216452079683732113456399844060553622) * 10 ^ 70 +
        5248847560026454262595873601960531554869386178584007210940676041794947) * 10 ^ 70 +
        6898109459454006841586948325931692868916811682436643829236269858914560) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (399 - x)) = _
  rw [show 400 = 53 +
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
    rw [show 251 = 24 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (400 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (400 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_400 :
    recurrence4Scalar1Second.coeff 400 =
      ((((742978178941748170886827367088712333875419381218692335940 * 10 ^ 70 +
        9024107151929752965627821015965800895180962957097799277757925846935004) * 10 ^ 70 +
        7325165022709702302764767064611781423924463998767082630224978689789219) * 10 ^ 70 +
        6452384537835865004416457501658561385403806311338970460429177087404617) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (400 - x)) = _
  rw [show 401 = 54 +
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
    rw [show 251 = 23 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (401 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (401 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_401 :
    recurrence4Scalar1Second.coeff 401 =
      -((((263398897623226579979896224658357513026430615901688924190 * 10 ^ 70 +
        5190837913363070424686539317151805019937167471101760692149274709657560) * 10 ^ 70 +
        9660239634447850519499033996877818485436740808084169966004224053240884) * 10 ^ 70 +
        1176158835718869397718012370309820905148336699197347580273575770118484) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (401 - x)) = _
  rw [show 402 = 55 +
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
    rw [show 251 = 22 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (402 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (402 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_402 :
    recurrence4Scalar1Second.coeff 402 =
      ((((89392919438089763252981769749797085538482241558609571685 * 10 ^ 70 +
        6916784713915625162760871468693601387915449147009088544200307056270390) * 10 ^ 70 +
        0448399171233567944076928769892692755616049580381364688180617891214243) * 10 ^ 70 +
        6138610837419771181609162787702036626261352416706494271576721861335409) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (402 - x)) = _
  rw [show 403 = 56 +
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
    rw [show 251 = 21 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (403 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (403 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_403 :
    recurrence4Scalar1Second.coeff 403 =
      -((((28997119952656436041085930824992259969949754476495090429 * 10 ^ 70 +
        7132192206260266026183243056385271373427740878895995133004561918756294) * 10 ^ 70 +
        9830465896952407962195103450770626894435655063529350427934006336799734) * 10 ^ 70 +
        3212709467167668482246280936875627669900523911565603976719118114642782) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (403 - x)) = _
  rw [show 404 = 57 +
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
    rw [show 251 = 20 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (404 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (404 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_404 :
    recurrence4Scalar1Second.coeff 404 =
      ((((8983144373445242728139653131654805412887565304147445391 * 10 ^ 70 +
        4496809768591379969418478115625986763440640959630021259080816476007334) * 10 ^ 70 +
        9137624640028622169623763065847999574118631207536639956019140293426452) * 10 ^ 70 +
        5607343174924581573689399221770765285532929551900313586620620747391741) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (404 - x)) = _
  rw [show 405 = 58 +
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
    rw [show 251 = 19 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (405 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (405 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_405 :
    recurrence4Scalar1Second.coeff 405 =
      -((((2654787663030337393970448933558078904442875816733174517 * 10 ^ 70 +
        5468912202284989367766881914484002181329363826580728678105918531265323) * 10 ^ 70 +
        9110966640779328971418580556735350962924259145979678913477179834092921) * 10 ^ 70 +
        1025761132369282620712343656285896920389617368655032046167515130470869) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (405 - x)) = _
  rw [show 406 = 59 +
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
    rw [show 251 = 18 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (406 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (406 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_406 :
    recurrence4Scalar1Second.coeff 406 =
      ((((745914191357733490484398350905975543433457816028463456 * 10 ^ 70 +
        5334222777088829554427719957514775412388555740673448026488109950681275) * 10 ^ 70 +
        1062058925473400307011627792775949725431901495994351997041661646915054) * 10 ^ 70 +
        6098999935893646637640645977286400967533676140972149638706126167902312) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (406 - x)) = _
  rw [show 407 = 60 +
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
    rw [show 251 = 17 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (407 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (407 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_407 :
    recurrence4Scalar1Second.coeff 407 =
      -((((197342839341418878219543182672673524861221309490617512 * 10 ^ 70 +
        6036263242084132743732641261260255418980905092164227908179947624067574) * 10 ^ 70 +
        1269573849598008756798580331674321662020737955562280392122518227650948) * 10 ^ 70 +
        6022730830277963705584126926026992755485927946656389946536872655668999) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (407 - x)) = _
  rw [show 408 = 61 +
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
    rw [show 251 = 16 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (408 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (408 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_408 :
    recurrence4Scalar1Second.coeff 408 =
      ((((47902661510314414373161104658148306899162354191328915 * 10 ^ 70 +
        1691071244616130893359239447831646068976578924419856784093677171334848) * 10 ^ 70 +
        6629506460813541603284075074929838364894904695578478851419347717592729) * 10 ^ 70 +
        4264280381618772696937813316437392979104031491472158377688973899495414) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (408 - x)) = _
  rw [show 409 = 62 +
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
    rw [show 251 = 15 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (409 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (409 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_409 :
    recurrence4Scalar1Second.coeff 409 =
      -((((9888178047154955098936672731725328940299791233878747 * 10 ^ 70 +
        3999524106434544538808496445311943465541052001163502215232975928377601) * 10 ^ 70 +
        8277396069389645658879835336079872543478968662632279560186707593551899) * 10 ^ 70 +
        1838027704033591142725925084768929552827508183429492985214569175913783) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (409 - x)) = _
  rw [show 410 = 63 +
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
    rw [show 251 = 14 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (410 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (410 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_410 :
    recurrence4Scalar1Second.coeff 410 =
      ((((1233732051721120079181612641539979474224460381414854 * 10 ^ 70 +
        6274287230530843290460299046354790596310221512537424602579805372096023) * 10 ^ 70 +
        5165784033065261779439585085486806844363003342629953732130938828054477) * 10 ^ 70 +
        5522053189021253890413656253037026072987377601914028443165172275477357) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (410 - x)) = _
  rw [show 411 = 64 +
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
    rw [show 251 = 13 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (411 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (411 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_411 :
    recurrence4Scalar1Second.coeff 411 =
      ((((294108853948480222233184489565782743275439494589416 * 10 ^ 70 +
        8717313900302285659073011820490500048405902146327198828225327036021883) * 10 ^ 70 +
        0157417949461032369727898948064515807230217436203464829016093521464109) * 10 ^ 70 +
        3605653711401100289758448365808318038160161727760973299331616622022076) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (411 - x)) = _
  rw [show 412 = 65 +
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
    rw [show 251 = 12 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (412 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (412 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_412 :
    recurrence4Scalar1Second.coeff 412 =
      -((((341077610711211461005612782330880983742121270508324 * 10 ^ 70 +
        1705097736233375397450142309638556368845658699859409089385133791770717) * 10 ^ 70 +
        7102503539297635480349691365596846369083277840240546508858082320480984) * 10 ^ 70 +
        2375657528119136677374238911083049116918237314728505834939106041437493) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (412 - x)) = _
  rw [show 413 = 66 +
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
    rw [show 251 = 11 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (413 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (413 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_413 :
    recurrence4Scalar1Second.coeff 413 =
      ((((197477222157082698374849120849098991125193899213722 * 10 ^ 70 +
        9948305409927756407585236840959004967096214626211390144333808417970638) * 10 ^ 70 +
        4734755489185461885395371537426848304155296334402744937622481193398773) * 10 ^ 70 +
        9605084200524773525423458947477408209753177809015252489561329048148259) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (413 - x)) = _
  rw [show 414 = 67 +
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
    rw [show 251 = 10 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (414 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (414 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_414 :
    recurrence4Scalar1Second.coeff 414 =
      -((((94535290540730888657245240031525848465812096611607 * 10 ^ 70 +
        5389408587264609688722747866030007857716902468379061490198889668708797) * 10 ^ 70 +
        6908021595094153194990102059651895215009686954258950366088295409613855) * 10 ^ 70 +
        2088794875480082463930753574374612538615399923982630024661399964596285) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (414 - x)) = _
  rw [show 415 = 68 +
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
    rw [show 251 = 9 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (415 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (415 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_415 :
    recurrence4Scalar1Second.coeff 415 =
      ((((41268957385494173543071587671950933589508329080501 * 10 ^ 70 +
        3834051136327395010366074149123265468972488847501687820101646386253751) * 10 ^ 70 +
        8699729570491338269549873102031372645796225821455863251777007690251333) * 10 ^ 70 +
        7094221566661472068782727742751581921119464943460130765452420246320781) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (415 - x)) = _
  rw [show 416 = 69 +
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
    rw [show 251 = 8 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (416 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (416 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_416 :
    recurrence4Scalar1Second.coeff 416 =
      -((((17051840138319194478383567872885347751180022896427 * 10 ^ 70 +
        0933337421692339075797431568107584331734728707987734120845344035500200) * 10 ^ 70 +
        2946247031089326189265029983426504663129805577486828128449048651660195) * 10 ^ 70 +
        8414595976496944241586262645464639232111260695818640543415545946581704) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (416 - x)) = _
  rw [show 417 = 70 +
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
    rw [show 251 = 7 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (417 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (417 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_417 :
    recurrence4Scalar1Second.coeff 417 =
      ((((6792824170961851250989868128091885557430290243776 * 10 ^ 70 +
        2592969955504189703290541344721703593436275592951413945484541826703186) * 10 ^ 70 +
        0181347929104868434086199949829275691791427863258256083422340054132420) * 10 ^ 70 +
        0484235682106909039229744307198637894006223045882025332175906983784959) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (417 - x)) = _
  rw [show 418 = 71 +
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
    rw [show 251 = 6 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (418 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (418 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_418 :
    recurrence4Scalar1Second.coeff 418 =
      -((((2635084378187742843847808356491551305592611648476 * 10 ^ 70 +
        0704101632420489504764706282868664756313340921559085039897014858254303) * 10 ^ 70 +
        7752954432994996363385380723560256918314728606735228542168280309312820) * 10 ^ 70 +
        4663334939891022916291384833132310982702721135919612293536040772661870) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (418 - x)) = _
  rw [show 419 = 72 +
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
    rw [show 251 = 5 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (419 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (419 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_419 :
    recurrence4Scalar1Second.coeff 419 =
      ((((1000173412986725711208023835696053343998185436732 * 10 ^ 70 +
        6010313038373899803907547079800599626613580590231780655025329714987598) * 10 ^ 70 +
        3683313063508270122181915758316268313894440524169103319254187046550115) * 10 ^ 70 +
        8872957509216936008890802716359829686407551785551172188892864776065654) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (419 - x)) = _
  rw [show 420 = 73 +
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
    rw [show 251 = 4 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (420 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (420 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_420 :
    recurrence4Scalar1Second.coeff 420 =
      -((((371807829502799115737428518600650730125893555126 * 10 ^ 70 +
        3402912972602730029291739440809867361840307521720354815349895454668564) * 10 ^ 70 +
        6439364709746062384220037588182295405840226515553789021303587184947934) * 10 ^ 70 +
        4955977102069595720397397899356242098432805326393474230191489891709849) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (420 - x)) = _
  rw [show 421 = 74 +
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
    rw [show 251 = 3 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (421 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (421 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_421 :
    recurrence4Scalar1Second.coeff 421 =
      ((((135133022265201231139049451105247412198414432588 * 10 ^ 70 +
        1031497525840819225874081035631880979906067683464615188597501137794612) * 10 ^ 70 +
        9312683302483185944427913052297406296440166642341263488709646422870318) * 10 ^ 70 +
        7469604602865738430569179306477843692460424281442697507211050241215953) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (421 - x)) = _
  rw [show 422 = 75 +
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
    rw [show 251 = 2 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (422 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (422 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_422 :
    recurrence4Scalar1Second.coeff 422 =
      -((((47850735820392956004737170549187487486113020728 * 10 ^ 70 +
        3371704252523713532473502788727761821665643153957568088402714289608321) * 10 ^ 70 +
        3832527109040747624400330064346220074178535687778482635399479537725372) * 10 ^ 70 +
        0939289201914682967579761552888905091679512785924917162666178273059471) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (422 - x)) = _
  rw [show 423 = 76 +
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
    rw [show 251 = 1 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (423 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (423 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_423 :
    recurrence4Scalar1Second.coeff 423 =
      ((((16436319519639913897030926971795301807640125765 * 10 ^ 70 +
        1793472922111998073867373991467653897266415034915732510307951725267786) * 10 ^ 70 +
        0252675012410749541844636497354945410681563431122071123946117000527773) * 10 ^ 70 +
        8184430346104323046616169028637572913406429857558199811966426390059326) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (423 - x)) = _
  rw [show 424 = 77 +
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
  rw [recurrence4Scalar1Second_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (424 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (424 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_424 :
    recurrence4Scalar1Second.coeff 424 =
      -((((5451070772146209660234931260089090343272142834 * 10 ^ 70 +
        4659980405412243157190456280644538591261979490376134277891482763311154) * 10 ^ 70 +
        7980665778299842959810313167599282263643531510912603188077545050842231) * 10 ^ 70 +
        4787273927024854043327365934964246683958420673106979599420242392822999) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (424 - x)) = _
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
    rw [show 283 = 31 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (425 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (425 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_425 :
    recurrence4Scalar1Second.coeff 425 =
      ((((1737234751157640820060612544982955198813623533 * 10 ^ 70 +
        7917624430182788857106933175064232949929599333479932457902189438387938) * 10 ^ 70 +
        9181140969364269309071017455706383106691383228830404579608532245641643) * 10 ^ 70 +
        1524381437024518209370380518074263054097912201251965862098422800799647) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (425 - x)) = _
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
    rw [show 283 = 30 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (426 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (426 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_426 :
    recurrence4Scalar1Second.coeff 426 =
      -((((529412457316632246534172512706837625248289062 * 10 ^ 70 +
        0742459749091351718402176664617351895095142180115308806162553462833862) * 10 ^ 70 +
        4892369226667352647065444943542960999190661113644520747076979244206759) * 10 ^ 70 +
        4125055939854240974697856377796908198882755180272826950258736857538911) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (426 - x)) = _
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
    rw [show 283 = 29 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (427 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (427 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_427 :
    recurrence4Scalar1Second.coeff 427 =
      ((((153422298173867828091172049431776081478930736 * 10 ^ 70 +
        8281037521817512420142235823923894987486977323848290614885378049379147) * 10 ^ 70 +
        8537007069037064378033212781461957070625019849028827309135995535165208) * 10 ^ 70 +
        0866614013086360220722089730221564332111022750922892956699740352537649) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (427 - x)) = _
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
    rw [show 283 = 28 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (428 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (428 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_428 :
    recurrence4Scalar1Second.coeff 428 =
      -((((41988082481289730584289189769388474022453313 * 10 ^ 70 +
        7693837742436422345347659892730968419964341485732348358142779348386517) * 10 ^ 70 +
        9551709100800946740494894944483611636708421909451492442404912591227398) * 10 ^ 70 +
        2381973663089424221702830214254881679917135771268176037468473719082024) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (428 - x)) = _
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
    rw [show 283 = 27 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (429 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (429 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_429 :
    recurrence4Scalar1Second.coeff 429 =
      ((((10744851418692215432967219419970507566610085 * 10 ^ 70 +
        1464579179578927576982061696326823557064110427129607698485329602139093) * 10 ^ 70 +
        1435654820100714437214071532818508545278987550591709621809351310628345) * 10 ^ 70 +
        9449767094519232586761278650041147192486387837755741174194521277187377) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (429 - x)) = _
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
    rw [show 283 = 26 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (430 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (430 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_430 :
    recurrence4Scalar1Second.coeff 430 =
      -((((2529720105399123953160921069860764773701933 * 10 ^ 70 +
        7194580093163464077450055440937785557896598321655622999804878889330783) * 10 ^ 70 +
        8471147473703412304147707626966439105348583641966161378474656785737207) * 10 ^ 70 +
        3280975815047262828579134045373624053975746372669736570774043736324093) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (430 - x)) = _
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
    rw [show 283 = 25 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (431 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (431 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_431 :
    recurrence4Scalar1Second.coeff 431 =
      ((((531205487321655085151948105019997209066015 * 10 ^ 70 +
        2910732010946592519287718880227315462831915131489936710363460724704983) * 10 ^ 70 +
        5666851882753688458967609464449544909852651901888158086733122990860469) * 10 ^ 70 +
        2475003918938601869347856436588992305497232110753093557660419386333184) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (431 - x)) = _
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
    rw [show 283 = 24 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (432 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (432 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_432 :
    recurrence4Scalar1Second.coeff 432 =
      -((((92293160421528391693610906987671231981470 * 10 ^ 70 +
        8411123080066116221583514139556082031401215693767902989845672401313877) * 10 ^ 70 +
        1587618104894437688376834671828803733741272259238437252600824623241924) * 10 ^ 70 +
        5689438219381902584021118731506223909707603405015295274294104594235169) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (432 - x)) = _
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
    rw [show 283 = 23 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (433 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (433 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_433 :
    recurrence4Scalar1Second.coeff 433 =
      ((((9865534871663096497470216961597474778126 * 10 ^ 70 +
        7600840356744552718271856138070699105413216688285631671057749384113258) * 10 ^ 70 +
        0644235644129417412797316870197551179637393283600869534620694162676377) * 10 ^ 70 +
        2922484042333529615372816545184022612736848000355742567965362125169306) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (433 - x)) = _
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
    rw [show 283 = 22 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (434 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (434 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_434 :
    recurrence4Scalar1Second.coeff 434 =
      ((((1277314558572554937260862677237733571596 * 10 ^ 70 +
        7194696209167775395388160539186286945606547756839888748138506697414264) * 10 ^ 70 +
        6482864011725457108950797121826933591053813692805432256297370085063066) * 10 ^ 70 +
        8353193941311443860536048769889054304138901652478988354992180863122354) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (434 - x)) = _
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
    rw [show 283 = 21 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (435 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (435 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_435 :
    recurrence4Scalar1Second.coeff 435 =
      -((((1258341248498370616457025847042809136525 * 10 ^ 70 +
        5046873303226664767048547744094260953889135688096419247382664901151249) * 10 ^ 70 +
        5236188707441051869372655435103389149082000478757629261907769925985026) * 10 ^ 70 +
        5377872471446351571576587064784732214277905444728530570272841018900553) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (435 - x)) = _
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
    rw [show 283 = 20 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (436 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (436 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_436 :
    recurrence4Scalar1Second.coeff 436 =
      ((((521689453634931559915663054077059575808 * 10 ^ 70 +
        8836381586833548243580139493126647377784022214023217006517794477426959) * 10 ^ 70 +
        3144368632953912020837814535664004608077973961672886202580271613352720) * 10 ^ 70 +
        2611694337095562236469398597959385445545111568062252600534499337681999) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (436 - x)) = _
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
    rw [show 283 = 19 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (437 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (437 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_437 :
    recurrence4Scalar1Second.coeff 437 =
      -((((169140714934240128907386854967896714829 * 10 ^ 70 +
        8441630890784539228910542038446970006492757831522094708069542095390060) * 10 ^ 70 +
        6065733236568789141948007966044716248780071625278635228947996194756176) * 10 ^ 70 +
        9893069933939039869441395967474399916187910423718440827751131023718730) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (437 - x)) = _
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
    rw [show 283 = 18 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (438 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (438 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_438 :
    recurrence4Scalar1Second.coeff 438 =
      ((((47701491235600412546430556787133665113 * 10 ^ 70 +
        3818545074126602980992776768408120201073881050783571978230395341211058) * 10 ^ 70 +
        7346407898649191314310853848291700013359253088838212543375597376636687) * 10 ^ 70 +
        5713042147467019539498389472313527274333903251645359694926421884976916) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (438 - x)) = _
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
    rw [show 283 = 17 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (439 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (439 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_439 :
    recurrence4Scalar1Second.coeff 439 =
      -((((12143015170447985707380343957004830484 * 10 ^ 70 +
        9085895414648407573018052535483418097653350808169150823916393281300565) * 10 ^ 70 +
        9020437523130636039934148764547685205291221272517568829410960465627550) * 10 ^ 70 +
        4448012366725809037330412597074424471409516999580098783673882152881168) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (439 - x)) = _
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
    rw [show 283 = 16 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (440 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (440 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_440 :
    recurrence4Scalar1Second.coeff 440 =
      ((((2834093197715492165823315707975345677 * 10 ^ 70 +
        7660770748397118879519875348828225107805244776638543965251717640743014) * 10 ^ 70 +
        7225772638217509757514164552995808163118022482091308853126409507123224) * 10 ^ 70 +
        3780054230845178768654481323155217440904149600127154195038380111242812) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (440 - x)) = _
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
    rw [show 283 = 15 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (441 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (441 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_441 :
    recurrence4Scalar1Second.coeff 441 =
      -((((610201898672522398999722967457936120 * 10 ^ 70 +
        3368756903291421812357190480806696101652288967311236761804834178964742) * 10 ^ 70 +
        6621163411989907848394605010264624190076255491272543763965453602258721) * 10 ^ 70 +
        6883802407320188102496818717796311334301344332828586639642231711856508) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (441 - x)) = _
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
    rw [show 283 = 14 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (442 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (442 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_442 :
    recurrence4Scalar1Second.coeff 442 =
      ((((121262511445674957642617872110460457 * 10 ^ 70 +
        3229069730197936077784480283279593571300111878921280869845478607054109) * 10 ^ 70 +
        2728710011413459045739278960481301689186923841613069971348751341627263) * 10 ^ 70 +
        9178975083877407813037584367893669820220641495676298136009558204745145) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (442 - x)) = _
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
    rw [show 283 = 13 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (443 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (443 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_443 :
    recurrence4Scalar1Second.coeff 443 =
      -((((22147250232757464932069665865715125 * 10 ^ 70 +
        5900503869562678470557491932944145341593043731918416737932504844813724) * 10 ^ 70 +
        0790254732056240190048792633747587988686326039183230225400267683681814) * 10 ^ 70 +
        5766017266015467066786252392600652771470442639630615428603879138439385) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (443 - x)) = _
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
    rw [show 283 = 12 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (444 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (444 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_444 :
    recurrence4Scalar1Second.coeff 444 =
      ((((3680133955605443598312169743716964 * 10 ^ 70 +
        1178344328487360126145804318698578616673826166120440450002112309494942) * 10 ^ 70 +
        9504855780099776838557502039829478682412367519739317920140800052034680) * 10 ^ 70 +
        2070985285288328796489089522061235267475207243709823819996143109337155) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (444 - x)) = _
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
    rw [show 283 = 11 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (445 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (445 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_445 :
    recurrence4Scalar1Second.coeff 445 =
      -((((545343048244635067576609918316545 * 10 ^ 70 +
        1163606875448203521744650447894719397791022687970364047224792122700715) * 10 ^ 70 +
        8980596738924784257579577677711710293967890696362428026908470470236194) * 10 ^ 70 +
        7823753541515004101529738889029865588627379306724229025932090247511994) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (445 - x)) = _
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
    rw [show 283 = 10 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (446 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (446 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_446 :
    recurrence4Scalar1Second.coeff 446 =
      ((((69073958095257329092169318946068 * 10 ^ 70 +
        7707155463768189873694905723539415864700235644942604893720236614947135) * 10 ^ 70 +
        4487538555365643357905457715679320834140639585424939999770014938927948) * 10 ^ 70 +
        1848020980475422290503858848118339283221140813946792789447835515422310) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (446 - x)) = _
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
    rw [show 283 = 9 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (447 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (447 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_447 :
    recurrence4Scalar1Second.coeff 447 =
      -((((6663150314511347383757700046469 * 10 ^ 70 +
        7306415635447455102807512487875296617548097065247185958036900667414608) * 10 ^ 70 +
        4250662025562805780128269835002615741929431352830230489664110353221877) * 10 ^ 70 +
        4683726679236841287261320412654837265839504601405501616918851616806922) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (447 - x)) = _
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
    rw [show 283 = 8 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (448 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (448 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_448 :
    recurrence4Scalar1Second.coeff 448 =
      ((((249114353396347346609473847117 * 10 ^ 70 +
        1743761059086590697944270413017381876680368243327143129592199191018831) * 10 ^ 70 +
        7475179620483886423977318012599749044634829612624918137053280658861662) * 10 ^ 70 +
        6015019017367976763396166413511185121819735366369808964213216204533326) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (448 - x)) = _
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
    rw [show 283 = 7 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (449 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (449 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_449 :
    recurrence4Scalar1Second.coeff 449 =
      ((((82347343361108022464160625882 * 10 ^ 70 +
        6715146443615882751017809716337340318236332783841486994323993508865266) * 10 ^ 70 +
        6486808143994354805239084648369791402267064939249444492905447892517587) * 10 ^ 70 +
        1420629545280688993019955681346453518142199257874022371118349336005619) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (449 - x)) = _
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
    rw [show 283 = 6 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (450 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (450 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_450 :
    recurrence4Scalar1Second.coeff 450 =
      -((((27108641376715287201044496152 * 10 ^ 70 +
        7362908783752558636603002907123357912123169339710069368082805535438867) * 10 ^ 70 +
        4871930068468338267955807498019152832227505524657089398948927073467708) * 10 ^ 70 +
        3504331513140061089495243174355005102963235577083158982185615878574003) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (450 - x)) = _
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
    rw [show 283 = 5 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (451 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (451 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_451 :
    recurrence4Scalar1Second.coeff 451 =
      ((((5216481565002700763796217778 * 10 ^ 70 +
        0766064563936181887193722279153434946878789748967169869986249162602188) * 10 ^ 70 +
        7708882690327228255509948785354395545844783344015732796675744554523701) * 10 ^ 70 +
        8817893538300532413044985900144949717657914945685193414203812725209550) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (451 - x)) = _
  rw [show 452 = 105 +
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
  rw [recurrence4Scalar1Second_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (452 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (452 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_452 :
    recurrence4Scalar1Second.coeff 452 =
      -((((749582790445526352527750500 * 10 ^ 70 +
        1256578385492888280041107626109610200437214290290339310375107590727859) * 10 ^ 70 +
        6874040876477797174468483772339328777573846275381975421680961391134268) * 10 ^ 70 +
        7219223814695212053470871422377256111121886937483585150182024157317784) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (452 - x)) = _
  rw [show 453 = 106 +
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
  rw [recurrence4Scalar1Second_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (453 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (453 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_453 :
    recurrence4Scalar1Second.coeff 453 =
      ((((79204976205651100875261652 * 10 ^ 70 +
        7269639131466920169037146649086249978306339736172754779240457478120077) * 10 ^ 70 +
        3533135953539571789714414155433008461229216090448046629406504163899497) * 10 ^ 70 +
        0185596721824303587886897637266735820226506805860556854349759352650762) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (453 - x)) = _
  rw [show 454 = 107 +
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
  rw [recurrence4Scalar1Second_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (454 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (454 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_454 :
    recurrence4Scalar1Second.coeff 454 =
      -((((4384153245845823932938283 * 10 ^ 70 +
        9085831908115058936299892168952806000390502609464138177140572848553710) * 10 ^ 70 +
        3956350556676477599978621822509233132901050846927699728588314984468946) * 10 ^ 70 +
        5176457765473382653077203424134901749415829442086454063290237132752938) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (454 - x)) = _
  rw [show 455 = 108 +
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
  rw [recurrence4Scalar1Second_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (455 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (455 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_455 :
    recurrence4Scalar1Second.coeff 455 =
      -((((473686399559926208910036 * 10 ^ 70 +
        1440994976867615408426059015645857509349056500272879932344157720977557) * 10 ^ 70 +
        6236474466290716859243452754405437007414232116621506213374524036184734) * 10 ^ 70 +
        9686851738914542768788944784416068152833575511869461492327371690075178) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (455 - x)) = _
  rw [show 456 = 109 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (456 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (456 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_456 :
    recurrence4Scalar1Second.coeff 456 =
      ((((191019149610022007307476 * 10 ^ 70 +
        5146485898754404611667397183445087683028178096960181370632225601125350) * 10 ^ 70 +
        0895722293073166650665335175830401073201500540128709188429882110269542) * 10 ^ 70 +
        9035878181525354737172312715981075878273350297774922511373934191382313) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (456 - x)) = _
  rw [show 457 = 110 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 31 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (457 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (457 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_457 :
    recurrence4Scalar1Second.coeff 457 =
      -((((35096007235436363528214 * 10 ^ 70 +
        6765559211443597439059569817803888720835365711482725241994212826685039) * 10 ^ 70 +
        0486561333444847363893412665919924294804011612010472818873148511519545) * 10 ^ 70 +
        2074708308731091686240298415216491270305938370308026583259691182692541) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (457 - x)) = _
  rw [show 458 = 111 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 30 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (458 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (458 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_458 :
    recurrence4Scalar1Second.coeff 458 =
      ((((4581517873298164113874 * 10 ^ 70 +
        3654619866315196054315305167362879655163774313039767525678574000162866) * 10 ^ 70 +
        7793732534481366174787485374143383206965391804975088236270616528446765) * 10 ^ 70 +
        9565188165698255832392843002126324297025103457869220362445811069767734) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (458 - x)) = _
  rw [show 459 = 112 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 29 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (459 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (459 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_459 :
    recurrence4Scalar1Second.coeff 459 =
      -((((432545713237268264038 * 10 ^ 70 +
        8846847383545043158314531717237670604040683283187253076760867334503966) * 10 ^ 70 +
        7759074360307310239302396066988505246950798521853110995787266795126920) * 10 ^ 70 +
        9615757288492762735224653406365133445664728087775286139862216666053780) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (459 - x)) = _
  rw [show 460 = 113 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 28 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (460 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (460 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_460 :
    recurrence4Scalar1Second.coeff 460 =
      ((((22443323120204317865 * 10 ^ 70 +
        3410013717827997558040240449012850502408665595925033691079906513684455) * 10 ^ 70 +
        9879769897596063960971265068941528870495051051033936329265196706051764) * 10 ^ 70 +
        5863874211423848697719182350082369667480227280376537632349668590464934) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (460 - x)) = _
  rw [show 461 = 114 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 27 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (461 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (461 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_461 :
    recurrence4Scalar1Second.coeff 461 =
      ((((1441682357280730711 * 10 ^ 70 +
        7688935328864764646372857677043268790646886320081746303706829069519092) * 10 ^ 70 +
        5816161145829036261988579491668766092995711439859503463447578285203052) * 10 ^ 70 +
        1580809211267604623742053321043055142517248016412371198442522584422255) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (461 - x)) = _
  rw [show 462 = 115 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 26 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (462 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (462 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_462 :
    recurrence4Scalar1Second.coeff 462 =
      -((((567366559815404638 * 10 ^ 70 +
        3261158906198887007625323168279180881978545160286549861873064038554336) * 10 ^ 70 +
        8049939538697724238016677278199678556985975507013169691689038757453629) * 10 ^ 70 +
        4771197055534286551354133645942513283037355945709723437668507480616942) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (462 - x)) = _
  rw [show 463 = 116 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 25 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (463 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (463 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_463 :
    recurrence4Scalar1Second.coeff 463 =
      ((((89179515549669399 * 10 ^ 70 +
        7471784165632587326571919730928104607072599481613929598540289102395417) * 10 ^ 70 +
        5942249338509635669001259192721322721278112145171820906418575639484553) * 10 ^ 70 +
        3931590795946166258741877072175368917592270907646814717031078362560172) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (463 - x)) = _
  rw [show 464 = 117 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 24 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (464 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (464 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_464 :
    recurrence4Scalar1Second.coeff 464 =
      -((((9907765037948716 * 10 ^ 70 +
        0528331407780142528559935351341604566726421023888569266638041836039070) * 10 ^ 70 +
        6161227906461529936786617607001145986491832256710782263917737369692219) * 10 ^ 70 +
        1400946975851710891801267059874373967190164737504083867793826527482905) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (464 - x)) = _
  rw [show 465 = 118 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 23 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (465 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (465 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_465 :
    recurrence4Scalar1Second.coeff 465 =
      ((((834084604090698 * 10 ^ 70 +
        4757120470080650318328627491419764688272087199017530241065670679710034) * 10 ^ 70 +
        5800528569266408155580402076027335265561428326700697449699062808096724) * 10 ^ 70 +
        9655272990557246582812968166791290138733346581062508579414353615605788) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (465 - x)) = _
  rw [show 466 = 119 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 22 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (466 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (466 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_466 :
    recurrence4Scalar1Second.coeff 466 =
      -((((50577622808750 * 10 ^ 70 +
        8289160975793817982762427796455460714827102124705169139209567338548238) * 10 ^ 70 +
        1910367270746024379175830177549909578263732080692448314418240426318694) * 10 ^ 70 +
        2915005629145143496218221166227528812547068356611210199051499147385423) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (466 - x)) = _
  rw [show 467 = 120 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 21 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (467 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (467 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_467 :
    recurrence4Scalar1Second.coeff 467 =
      ((((1544924451846 * 10 ^ 70 +
        0760937211628028985112324312099525638728627377387159413466915222569805) * 10 ^ 70 +
        5721224172453197980800945255747555198182358634755437228896430504041336) * 10 ^ 70 +
        8721462947220158694961971591651759696296982263263126932028319830509718) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (467 - x)) = _
  rw [show 468 = 121 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 20 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (468 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (468 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_468 :
    recurrence4Scalar1Second.coeff 468 =
      ((((91019881947 * 10 ^ 70 +
        7958435466353293113454652865396365160656867327501740681984914246977184) * 10 ^ 70 +
        7245939958660163815258265318294981439440865712330621993441941767775796) * 10 ^ 70 +
        8974825150961522288963795549524251788212015110402846082993047946576950) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (468 - x)) = _
  rw [show 469 = 122 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 19 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (469 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (469 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_469 :
    recurrence4Scalar1Second.coeff 469 =
      -((((18343279733 * 10 ^ 70 +
        8746310490134331309021774639725432994067528057697815354321558827791967) * 10 ^ 70 +
        0911514547680088673779882532148798455654741735932245737813387346592695) * 10 ^ 70 +
        1465464435858418106382321023353567487619838472030834427374078397022875) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (469 - x)) = _
  rw [show 470 = 123 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 18 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (470 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (470 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_470 :
    recurrence4Scalar1Second.coeff 470 =
      ((((1585475709 * 10 ^ 70 +
        7645206472878005895511997967913024982324003528615983030743807059241751) * 10 ^ 70 +
        7260196797527650494185715626368187276243934355755832372218279003223610) * 10 ^ 70 +
        9997363018593189682439833267690145781072010975318815468367461822952505) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (470 - x)) = _
  rw [show 471 = 124 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 17 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (471 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (471 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_471 :
    recurrence4Scalar1Second.coeff 471 =
      -((((88426205 * 10 ^ 70 +
        4968395513310987935922468989234602434515188314208698862354687581812259) * 10 ^ 70 +
        2997593137551502713008340347608044106642980438683787606818514929118399) * 10 ^ 70 +
        3614398183005879834738514946863348574140808180259418404003158390067578) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (471 - x)) = _
  rw [show 472 = 125 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 16 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (472 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (472 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_472 :
    recurrence4Scalar1Second.coeff 472 =
      ((((2949587 * 10 ^ 70 +
        2984655671956189616080283372341283159972745116942579896765990049284942) * 10 ^ 70 +
        2394425976300166117202826951547767595278237595301183029194983760600329) * 10 ^ 70 +
        1856101929255838676224826293681861678253799064553991939772454120177080) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (472 - x)) = _
  rw [show 473 = 126 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 15 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (473 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (473 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_473 :
    recurrence4Scalar1Second.coeff 473 =
      -((((8480 * 10 ^ 70 +
        4062256670430238107098051059099171466903496733416305706613481137990626) * 10 ^ 70 +
        1588336253993018278164959393985064325341257677613975849739983794460146) * 10 ^ 70 +
        6085154919660733345219046821530688881279347556210853002551342126947590) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (473 - x)) = _
  rw [show 474 = 127 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 14 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (474 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (474 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_474 :
    recurrence4Scalar1Second.coeff 474 =
      -((((5383 * 10 ^ 70 +
        5507487619176533618821196324957796522047594029694554317496660138912428) * 10 ^ 70 +
        2119363272602500518536250337703561326989474854462064712212840323482748) * 10 ^ 70 +
        2642594222784148618331405653534334067477561070534166863525150186252902) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (474 - x)) = _
  rw [show 475 = 128 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 13 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (475 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (475 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_475 :
    recurrence4Scalar1Second.coeff 475 =
      ((((324 * 10 ^ 70 +
        6189776805208155305956146002345574056460404811393284207769810334298913) * 10 ^ 70 +
        0306619364623560185365244456249008507454500100917087119709892187581885) * 10 ^ 70 +
        7053321562663506432088148135834741247317110982927380942025990315967698) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (475 - x)) = _
  rw [show 476 = 129 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 12 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (476 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (476 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_476 :
    recurrence4Scalar1Second.coeff 476 =
      -((((8 * 10 ^ 70 +
        7989105693678167274757480431326829754256556362813718342227019117872850) * 10 ^ 70 +
        3350077518165092530489711854410633375920371215862553015877263021699183) * 10 ^ 70 +
        1911758053260743213431722195960731353029175831623332895880489907383616) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (476 - x)) = _
  rw [show 477 = 130 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 11 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (477 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (477 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_477 :
    recurrence4Scalar1Second.coeff 477 =
      (((196466627747958759453827042799814559471602787184527290150702577242808 * 10 ^ 70 +
        0435886928946116580823412936563408396900906050478620190649060463634711) * 10 ^ 70 +
        4224652764726604138745262623916300687753525086652514619849067592594823) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (477 - x)) = _
  rw [show 478 = 131 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 10 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (478 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (478 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_478 :
    recurrence4Scalar1Second.coeff 478 =
      (((64040068575171941540421377164470683039991094327871264648431700590749 * 10 ^ 70 +
        6828526587496148958938928345668830455038361092006658459664011538270048) * 10 ^ 70 +
        3019141021246222130850136006522531923018735588102414122947628212621733) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (478 - x)) = _
  rw [show 479 = 132 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 9 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (479 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (479 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_479 :
    recurrence4Scalar1Second.coeff 479 =
      -(((1693585157580120967959775794019236823882557577610219235013823675059 * 10 ^ 70 +
        1987761532862521165001718274672105536641002298218225500993352394649733) * 10 ^ 70 +
        4010124984722708573917236082626030441872620983450668829900021919065097) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (479 - x)) = _
  rw [show 480 = 133 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 8 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_479_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (480 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (480 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_480 :
    recurrence4Scalar1Second.coeff 480 =
      (((428476796876125402629712499761083863137262312457274023074506165 * 10 ^ 70 +
        5821861131635910850149819542949354326263362240117688414786375518010477) * 10 ^ 70 +
        0324400998211935663345885798760241452897384428430418236613182853900282) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (480 - x)) = _
  rw [show 481 = 134 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 7 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_480_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (481 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (481 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_481 :
    recurrence4Scalar1Second.coeff 481 =
      (((571620929562550029966431625721047329796733360869817049113254062 * 10 ^ 70 +
        6366549521343627158179798987345895001937364733753782231369976149994968) * 10 ^ 70 +
        5891765091670282535978187420286377623916784896195974935214465791173872) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (481 - x)) = _
  rw [show 482 = 135 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 6 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_481_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (482 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (482 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_482 :
    recurrence4Scalar1Second.coeff 482 =
      -(((3737142562596350340282869761772721630562141053681895513326655 * 10 ^ 70 +
        1990628007641376920732567489993912548162034724799772267010230400454695) * 10 ^ 70 +
        3221948328984620313037461278607904447002614288350536323513535891927386) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (482 - x)) = _
  rw [show 483 = 136 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 5 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_482_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (483 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (483 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_483 :
    recurrence4Scalar1Second.coeff 483 =
      -(((91310160464374603435474983446296302341011409367853177217294 * 10 ^ 70 +
        7593641876362595139483609991298344515917770323429099078824620213580538) * 10 ^ 70 +
        4280273193814692449245729147072212814023759519922465361581510025906391) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (483 - x)) = _
  rw [show 484 = 137 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 4 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_483_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (484 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (484 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_484 :
    recurrence4Scalar1Second.coeff 484 =
      (((503607785877125461216791671980561889662996031852569481867 * 10 ^ 70 +
        7811584684576150408454181957290438767188406229998696564912333482524741) * 10 ^ 70 +
        7769049816666811792696168116900941160111916767247598012619684706889308) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (484 - x)) = _
  rw [show 485 = 138 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 3 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_484_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (485 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (485 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_485 :
    recurrence4Scalar1Second.coeff 485 =
      (((8823474851882803396966561030215947312626624428342736264 * 10 ^ 70 +
        1852137595014304017746269507022919685741469091176869885844097778669457) * 10 ^ 70 +
        4823858464842038544504647959637629947272083259276399762457573745004136) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (485 - x)) = _
  rw [show 486 = 139 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 2 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_485_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (486 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 314,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (486 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_486 :
    recurrence4Scalar1Second.coeff 486 =
      -(((15443979115698218761741592105477302784630367147418353 * 10 ^ 70 +
        0610720933701431880288129709331757360022823357873868233516544427491462) * 10 ^ 70 +
        1845238348011298199660170005965280564552512852986089001779116070892601) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (486 - x)) = _
  rw [show 487 = 140 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 1 +
      314 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_486_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (487 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 315,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (487 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_487 :
    recurrence4Scalar1Second.coeff 487 =
      -(((414991830024141681352849091350987095830077968525406 * 10 ^ 70 +
        4848257356406484316545618153618779686069951193553143975749586052394700) * 10 ^ 70 +
        5258522108721075412387843053100449961337538296608914773848108386274649) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (487 - x)) = _
  rw [show 488 = 141 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_487_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (488 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 316,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (488 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_488 :
    recurrence4Scalar1Second.coeff 488 =
      -(((180835326184285261155226649537635196096714204935 * 10 ^ 70 +
        0595418512106716759213158519204934912742824909650373021638295283799807) * 10 ^ 70 +
        2390692148124191076969529476911001265588485248206344983389636925827149) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (488 - x)) = _
  rw [show 489 = 142 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 31 +
      316 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_488_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (489 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 317,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (489 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_489 :
    recurrence4Scalar1Second.coeff 489 =
      (((9448806636804312360496517657655598586428830607 * 10 ^ 70 +
        9073275476776622384064046035284981158944800948592895049446660597817790) * 10 ^ 70 +
        0090847016001479759754224480879902591692694786824242933061318059702154) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (489 - x)) = _
  rw [show 490 = 143 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 30 +
      317 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_489_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (490 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 318,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (490 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_490 :
    recurrence4Scalar1Second.coeff 490 =
      (((13268362530418391969483744763926907173517557 * 10 ^ 70 +
        3407844680097043394465627347661788007457889530532008708600176011086801) * 10 ^ 70 +
        0479263791774207306251636426766672063621438544982793256977315648501248) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (490 - x)) = _
  rw [show 491 = 144 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 29 +
      318 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_490_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (491 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 319,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (491 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_491 :
    recurrence4Scalar1Second.coeff 491 =
      -(((113209488106153907372421075445718236847353 * 10 ^ 70 +
        2928468908636814721030231213597463900887240123546467071598148701144117) * 10 ^ 70 +
        8883867276876809491940810176250168986250552165006871609551325338415128) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (491 - x)) = _
  rw [show 492 = 145 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 28 +
      319 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_491_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (492 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 320,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (492 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_492 :
    recurrence4Scalar1Second.coeff 492 =
      -(((187130597456029077725859149552309111926 * 10 ^ 70 +
        2086694780174440722484189682676091203927774883403422903201212023161256) * 10 ^ 70 +
        8792667227447256532427023516535831234693439513014924947748171839096098) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (492 - x)) = _
  rw [show 493 = 146 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 27 +
      320 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_492_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (493 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 321,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (493 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_493 :
    recurrence4Scalar1Second.coeff 493 =
      (((823467456313195213771518000070212063 * 10 ^ 70 +
        7673598806356140531890592141615084703582504721906342048949597467486266) * 10 ^ 70 +
        9046612880325377457759754812327627030510554185144026037771706388253797) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (493 - x)) = _
  rw [show 494 = 147 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 26 +
      321 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_493_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (494 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 322,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (494 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_494 :
    recurrence4Scalar1Second.coeff 494 =
      (((1144958322528545393309164698806488 * 10 ^ 70 +
        8940553893853040044059251539127746008741036105434547383369719567378874) * 10 ^ 70 +
        4605281417332689900485087531914578335001862313249786922928499628290530) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (494 - x)) = _
  rw [show 495 = 148 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 25 +
      322 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_494_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (495 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 323,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (495 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_495 :
    recurrence4Scalar1Second.coeff 495 =
      -(((3858781672019701146761944630437 * 10 ^ 70 +
        6969819127695799440930547647982369313329982923591823768027258389547771) * 10 ^ 70 +
        4514116914319131071223466245772445024737369302655386199580672190456428) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (495 - x)) = _
  rw [show 496 = 149 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 24 +
      323 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_495_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (496 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 324,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (496 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_496 :
    recurrence4Scalar1Second.coeff 496 =
      -(((2914642532745357987849584494 * 10 ^ 70 +
        7791516916577962667169486923496557639193230096978953531491163618876647) * 10 ^ 70 +
        7095174320078484426345997359175275415086828783749459809156472295888909) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (496 - x)) = _
  rw [show 497 = 150 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 23 +
      324 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_496_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (497 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 325,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (497 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_497 :
    recurrence4Scalar1Second.coeff 497 =
      (((10676793028618028619297164 * 10 ^ 70 +
        1387704226385524311746061655963603700792953570837443603298287326947210) * 10 ^ 70 +
        3150347459381080369328587017683222114912595795804930105785874164396730) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (497 - x)) = _
  rw [show 498 = 151 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 22 +
      325 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_497_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (498 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 326,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (498 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_498 :
    recurrence4Scalar1Second.coeff 498 =
      (((498275475290253477980 * 10 ^ 70 +
        3573276851072117120171245449828655281146225980186056564849767780746097) * 10 ^ 70 +
        3292920331388228243059197878226536765647006937081767531181907561917936) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (498 - x)) = _
  rw [show 499 = 152 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 21 +
      326 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_498_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (499 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 327,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (499 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_499 :
    recurrence4Scalar1Second.coeff 499 =
      -(((12525898769111084400 * 10 ^ 70 +
        8773622584775467135416684843805051672344853108251101956691145581053919) * 10 ^ 70 +
        7164777588629938298963481807580554783364375443841388222129875373820313) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (499 - x)) = _
  rw [show 500 = 153 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 20 +
      327 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_499_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (500 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 328,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (500 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_500 :
    recurrence4Scalar1Second.coeff 500 =
      (((5061279413415154 * 10 ^ 70 +
        8145340483400820941356609238987881895312261185186296061559929492959301) * 10 ^ 70 +
        2582043291566060341080335322655810642253637351441892815035516568296707) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (500 - x)) = _
  rw [show 501 = 154 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 19 +
      328 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_500_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (501 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 329,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (501 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_501 :
    recurrence4Scalar1Second.coeff 501 =
      (((2935661162827 * 10 ^ 70 +
        7629025178670272443668309558531455013254409874780961331929648077273646) * 10 ^ 70 +
        9953338096845147054407318940585437191052542332107865530770905227334575) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (501 - x)) = _
  rw [show 502 = 155 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 18 +
      329 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_501_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (502 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 330,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (502 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_502 :
    recurrence4Scalar1Second.coeff 502 =
      -(((1805537064 * 10 ^ 70 +
        1606851977881043721258292545609102823915863381776621261067480968083820) * 10 ^ 70 +
        2180556031644139488295891508789368075123680922439267775422090364076115) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (502 - x)) = _
  rw [show 503 = 156 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 17 +
      330 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_502_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (503 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 331,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (503 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_503 :
    recurrence4Scalar1Second.coeff 503 =
      (((82423 * 10 ^ 70 +
        9387061716548933247308941997599315202451016948887555236862431353380529) * 10 ^ 70 +
        3268889093167339402368555202257717611915665197484749038998933948769823) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (503 - x)) = _
  rw [show 504 = 157 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 16 +
      331 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_503_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (504 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 332,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (504 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_504 :
    recurrence4Scalar1Second.coeff 504 =
      (((65 * 10 ^ 70 +
        4003114374771688498456742444166169623069976997096750084210743000140871) * 10 ^ 70 +
        2134234563618719425972214203737222057207570712622547129205923769434988) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (504 - x)) = _
  rw [show 505 = 158 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 15 +
      332 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_504_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (505 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 333,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (505 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_505 :
    recurrence4Scalar1Second.coeff 505 =
      -((75860038365372498151803163494669045364877564914774519614011318111758 * 10 ^ 70 +
        4047376235502330786212080536737492814527851066441890334562571895345406) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (505 - x)) = _
  rw [show 506 = 159 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 14 +
      333 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_505_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (506 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 334,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (506 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_506 :
    recurrence4Scalar1Second.coeff 506 =
      -((443300449417990287791349829928449001319828619133474587218600898 * 10 ^ 70 +
        2450476323376636699453409418890258901663216071557213484330630732881731) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (506 - x)) = _
  rw [show 507 = 160 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 13 +
      334 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_506_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (507 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 335,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (507 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_507 :
    recurrence4Scalar1Second.coeff 507 =
      ((241822758168947522958542272395850146127790795507547499075563 * 10 ^ 70 +
        1903686262009571046428148183930110225363537965003320830308736499231935) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (507 - x)) = _
  rw [show 508 = 161 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 12 +
      335 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_507_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (508 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 336,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (508 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_508 :
    recurrence4Scalar1Second.coeff 508 =
      -((5100900081852533754983375618016425088102532057256682964 * 10 ^ 70 +
        8345348966081023532157843708349183330621733133710307021342705614954236) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (508 - x)) = _
  rw [show 509 = 162 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 11 +
      336 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_508_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (509 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 337,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (509 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_509 :
    recurrence4Scalar1Second.coeff 509 =
      -((21225988629101627378181389527248429964942603236371 * 10 ^ 70 +
        3416279635212241687203083830936590401081683513256407552117429395266514) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (509 - x)) = _
  rw [show 510 = 163 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 10 +
      337 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_509_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (510 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 338,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (510 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_510 :
    recurrence4Scalar1Second.coeff 510 =
      ((781704870313966052063291979338901743329384019 * 10 ^ 70 +
        5459367436458349431567625528897697871814485631550203301474854156464624) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (510 - x)) = _
  rw [show 511 = 164 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 9 +
      338 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_510_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (511 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 339,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (511 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_511 :
    recurrence4Scalar1Second.coeff 511 =
      -((2425765963424821799496870065135440609201 * 10 ^ 70 +
        6169267720949311568153140000756555282926293164642050112841356828591028) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (511 - x)) = _
  rw [show 512 = 165 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 8 +
      339 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_511_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (512 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 340,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (512 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_512 :
    recurrence4Scalar1Second.coeff 512 =
      -((1851907982886961883216133132670210 * 10 ^ 70 +
        5447329954539564972589951325266751903227725804105866716067951648065400) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (512 - x)) = _
  rw [show 513 = 166 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 7 +
      340 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_512_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Second_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (513 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1Second_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 341,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4QuotientConstant.coeff (513 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1Second_coeff_513 :
    recurrence4Scalar1Second.coeff 513 =
      ((7236652153748435013033965222 * 10 ^ 70 +
        7155559609147174920468232540338420952278872539000455352146412519648746) : ℚ) := by
  unfold recurrence4Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    remainder5Coefficient1.coeff x * recurrence4QuotientConstant.coeff (513 - x)) = _
  rw [show 514 = 167 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 6 +
      341 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Second_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Second_coeff_513_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
