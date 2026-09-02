/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1SecondPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
