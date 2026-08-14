/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0MainPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

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
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
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

attribute [local simp]
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar0Main_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (483 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (483 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_483 :
    recurrence4Scalar0Main.coeff 483 =
      -(((150295326141321194884286277676307783479914861623575175852964888729 * 10 ^ 70 +
        8697760048156549399003594194843261981909866387786281178003229218796843) * 10 ^ 70 +
        7674684626928705645035432459243666219182705116868908401841096204172858) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (483 - x)) = _
  rw [show 484 = 137 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 8 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (484 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (484 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_484 :
    recurrence4Scalar0Main.coeff 484 =
      (((255453492043152813589351361629421608400607048547418010944984807 * 10 ^ 70 +
        0110981115068309988068567048353973379029116511466274392423102974204150) * 10 ^ 70 +
        6909604333265658313416582629185696679368103674023667175306945118168299) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (484 - x)) = _
  rw [show 485 = 138 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 7 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (485 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (485 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_485 :
    recurrence4Scalar0Main.coeff 485 =
      (((49484638078864348050701241645715103080199050374073392871782828 * 10 ^ 70 +
        6760624528422648570848645861346644671718477541995627370596229144948561) * 10 ^ 70 +
        7497318676876129918837334693444020603751718472190601024067176743401740) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (485 - x)) = _
  rw [show 486 = 139 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 6 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (486 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (486 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_486 :
    recurrence4Scalar0Main.coeff 486 =
      -(((350434610957941411341154873319264460249414543242244831416658 * 10 ^ 70 +
        5735932679116121312025855814371288771675323238422075075101656217190120) * 10 ^ 70 +
        4535366542627808611867573570682247312395980028960470263724249213927554) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (486 - x)) = _
  rw [show 487 = 140 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 5 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (487 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (487 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_487 :
    recurrence4Scalar0Main.coeff 487 =
      -(((8025859165401998357811844055438664279676001560772679703928 * 10 ^ 70 +
        8519666516305052341231489986487233239965380438273346670974859759184708) * 10 ^ 70 +
        6689716531892598527714454520261301382315673447968392980961261757437379) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (487 - x)) = _
  rw [show 488 = 141 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 4 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (488 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (488 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_488 :
    recurrence4Scalar0Main.coeff 488 =
      (((43952942346819601352002321854502499860676165503287014895 * 10 ^ 70 +
        3649700090497791381551765883776271286385553940248672007625861606857687) * 10 ^ 70 +
        3281623461004823927948511314322123635566150012118403016422435216905409) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (488 - x)) = _
  rw [show 489 = 142 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 3 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (489 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (489 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_489 :
    recurrence4Scalar0Main.coeff 489 =
      (((779461770442700071914326936384233156540206035681947841 * 10 ^ 70 +
        2512326292711373779663981008560726738053971056120809960317239617379824) * 10 ^ 70 +
        2003076221961578504329585744592537658967134397658512017508727497573008) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (489 - x)) = _
  rw [show 490 = 143 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 2 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (490 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 314,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (490 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_490 :
    recurrence4Scalar0Main.coeff 490 =
      -(((1168950026196800071631463202222982896765497245835666 * 10 ^ 70 +
        0676725141050304013558828339896003735233019395075363393483337534651681) * 10 ^ 70 +
        9532415177540307033811466728480452103627664300853715544266008625288562) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (490 - x)) = _
  rw [show 491 = 144 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 1 +
      314 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (491 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 315,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (491 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_491 :
    recurrence4Scalar0Main.coeff 491 =
      -(((35963114777668247955841425751011502662071774187419 * 10 ^ 70 +
        6844215928706500991757076188605070749017482148332094287242902875250114) * 10 ^ 70 +
        7045887598759497334950879591927826050617157700307432146265612288768995) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (491 - x)) = _
  rw [show 492 = 145 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (492 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 316,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (492 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_492 :
    recurrence4Scalar0Main.coeff 492 =
      -(((24398737419289774414397015911376366471881971333 * 10 ^ 70 +
        7018068840138643021023650140253448428010336662168655811820114982787319) * 10 ^ 70 +
        3249169520716283805101602199480863673907960996560831034879381346433606) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (492 - x)) = _
  rw [show 493 = 146 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 31 +
      316 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (493 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 317,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (493 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_493 :
    recurrence4Scalar0Main.coeff 493 =
      (((790808903529406007963595342626397068367516465 * 10 ^ 70 +
        7112919265264958180915965061261408467253774383550852081357064558927576) * 10 ^ 70 +
        0887253134881018934479822556689777408356267212644130814760130607036490) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (493 - x)) = _
  rw [show 494 = 147 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 30 +
      317 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (494 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 318,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (494 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_494 :
    recurrence4Scalar0Main.coeff 494 =
      (((1281159807771521777463837050978551382875897 * 10 ^ 70 +
        2872260815651495018974414659885917645458343448018069513974805082000059) * 10 ^ 70 +
        4446111896967754524434957300651464471738106436212736480818451755564763) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (494 - x)) = _
  rw [show 495 = 148 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 29 +
      318 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (495 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 319,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (495 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_495 :
    recurrence4Scalar0Main.coeff 495 =
      -(((9170310921355321595303940877316557278812 * 10 ^ 70 +
        5523639901684763864055775890161396104325040243976989600041588667338383) * 10 ^ 70 +
        7192789575677918438224838480606875042903545510925000034948790625518017) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (495 - x)) = _
  rw [show 496 = 149 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 28 +
      319 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
