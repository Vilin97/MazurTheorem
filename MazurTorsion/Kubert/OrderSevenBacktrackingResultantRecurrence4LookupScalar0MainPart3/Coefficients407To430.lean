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

private theorem recurrence4Scalar0Main_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (407 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (407 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_407 :
    recurrence4Scalar0Main.coeff 407 =
      ((((39028774421958086257447613305402562363529923473656765179 * 10 ^ 70 +
        4717819444287517119273875871304931603483666237994911895662358897050456) * 10 ^ 70 +
        2966536683375865917126897141274507816845728457414179544867700389288434) * 10 ^ 70 +
        9617304643580144718759966840608981541383426225486636375001649617388760) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (407 - x)) = _
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
    rw [show 251 = 20 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (408 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (408 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_408 :
    recurrence4Scalar0Main.coeff 408 =
      -((((8964000261058307126814391453520881929125686327528402714 * 10 ^ 70 +
        0433736577371417607110130512497912502885711561015349355544119312740049) * 10 ^ 70 +
        6986674250028602358808524925891020672007991545738226883483582101907924) * 10 ^ 70 +
        8210134959414401237222455789949868076879970880375564161627280430223016) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (408 - x)) = _
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
    rw [show 251 = 19 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (409 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (409 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_409 :
    recurrence4Scalar0Main.coeff 409 =
      ((((1664105749617563679345692817388426278861317635180332474 * 10 ^ 70 +
        5223183527745265532970790202859475744504286553784179881836706859373295) * 10 ^ 70 +
        7180808267949927500395633392713421705278327244426500169895776796547854) * 10 ^ 70 +
        9772062451952125885670839704833400477976634267729471746486932830270639) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (409 - x)) = _
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
    rw [show 251 = 18 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (410 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (410 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_410 :
    recurrence4Scalar0Main.coeff 410 =
      -((((149766556825941774997446865007795969487330758343819882 * 10 ^ 70 +
        8393514558232241373795213335129257808228192422442477924402137395305950) * 10 ^ 70 +
        0370142688291043762772643035382730186571613805169924230546321905929153) * 10 ^ 70 +
        0590403399124698571091908722964806146178760555301703727978273518367862) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (410 - x)) = _
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
    rw [show 251 = 17 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (411 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (411 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_411 :
    recurrence4Scalar0Main.coeff 411 =
      -((((66262157431271441714949054837034886104856982619563906 * 10 ^ 70 +
        0634853284390129909581563235414197582129900068965387895023808974716969) * 10 ^ 70 +
        7088662026706078074745746751506475280440069301967240814417153178410814) * 10 ^ 70 +
        5470753527703393426480720602328110468670666310916021584472921316793375) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (411 - x)) = _
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
    rw [show 251 = 16 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (412 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (412 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_412 :
    recurrence4Scalar0Main.coeff 412 =
      ((((53419725886863333182127774784029864201238870142352609 * 10 ^ 70 +
        2636893815480644026176058562971553286972780167302628973048705177865884) * 10 ^ 70 +
        6951976009358705066068787935173122138791494159419170668915709383994235) * 10 ^ 70 +
        7111950555600106190237536511168133094295191804464153639499792769772117) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (412 - x)) = _
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
    rw [show 251 = 15 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (413 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (413 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_413 :
    recurrence4Scalar0Main.coeff 413 =
      -((((25780421242230113773126411839471571308646658403032341 * 10 ^ 70 +
        8674926280183950162075348516620252997484102013216279523817411329918695) * 10 ^ 70 +
        2397672490882085854097646020394206163631001651764695393376039077080717) * 10 ^ 70 +
        5158193232759738101353857290759833759189333842276447917024505953728470) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (413 - x)) = _
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
    rw [show 251 = 14 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (414 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (414 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_414 :
    recurrence4Scalar0Main.coeff 414 =
      ((((10536567011851746759490292540017339976873118530218575 * 10 ^ 70 +
        8004463024722578799878861378354597179829379480925353041527206648534729) * 10 ^ 70 +
        3988446924069976612363024014650298397345403063104838812628600062082390) * 10 ^ 70 +
        8216090157115719214666462199729325502553612101172056049775206040597426) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (414 - x)) = _
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
    rw [show 251 = 13 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (415 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (415 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_415 :
    recurrence4Scalar0Main.coeff 415 =
      -((((3985712011209159602504400317492107263498356151836432 * 10 ^ 70 +
        5084764580286017492401055985654942188451916200056303897068099429496926) * 10 ^ 70 +
        6396143382312943721442330633112940973036567722501004047574026157027642) * 10 ^ 70 +
        6137764404336625536018874478581352318152389228749747756466334143555188) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (415 - x)) = _
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
    rw [show 251 = 12 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (416 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (416 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_416 :
    recurrence4Scalar0Main.coeff 416 =
      ((((1455100091694705043064632848644975946483126750572407 * 10 ^ 70 +
        7565954285931512047561466084703823317133946247592113074980645733997699) * 10 ^ 70 +
        4422388651194374695368927950268556275627910528707463014912342193415422) * 10 ^ 70 +
        2422481197425969903615435795405902353052540399332379396040988069007218) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (416 - x)) = _
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
    rw [show 251 = 11 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (417 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (417 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_417 :
    recurrence4Scalar0Main.coeff 417 =
      -((((525977390856231324355255278547020923453805550624567 * 10 ^ 70 +
        1949377633970301217648566502178383482793838652346113266241565637904493) * 10 ^ 70 +
        8573679867631787196443135432945961657766721119994163035655537483057080) * 10 ^ 70 +
        1437621549762250183488344016676268772541641083700598229748331358622370) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (417 - x)) = _
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
    rw [show 251 = 10 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (418 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (418 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_418 :
    recurrence4Scalar0Main.coeff 418 =
      ((((191211412250795511278606702078965615806358673643833 * 10 ^ 70 +
        3574727596352945828987329315700544060499170202055177222553470913543579) * 10 ^ 70 +
        7455832949367272988446527945280426623496799790630851515866122920676644) * 10 ^ 70 +
        7421282706140835953248160791451925336039324392076349228207426594562229) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (418 - x)) = _
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
    rw [show 251 = 9 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (419 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (419 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_419 :
    recurrence4Scalar0Main.coeff 419 =
      -((((70363746421758527469968178473815901355108999851794 * 10 ^ 70 +
        9416031084215757641713418078420700741773602921479899907025937935741827) * 10 ^ 70 +
        9792701363248302124887721156521158054038932489478651431687585247589329) * 10 ^ 70 +
        8660132052227174649784690573521793631194841950934992998728837487241399) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (419 - x)) = _
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
    rw [show 251 = 8 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (420 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (420 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_420 :
    recurrence4Scalar0Main.coeff 420 =
      ((((26163713042925444761577881011699115233064806994716 * 10 ^ 70 +
        5068112850517025373001600116124870488130880788335697498902852356516919) * 10 ^ 70 +
        2359525842746192148004355946917666866137819767267054233595097814126532) * 10 ^ 70 +
        5097136540065829206313792036864752550643804106544815049766386468825587) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (420 - x)) = _
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
    rw [show 251 = 7 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (421 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (421 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_421 :
    recurrence4Scalar0Main.coeff 421 =
      -((((9757381443667367115622212174658304635653849929879 * 10 ^ 70 +
        1684723427897673083357832867400036484842257216625948993531023188661150) * 10 ^ 70 +
        8523528059835672892183562717834137724028377589796400541246215591341996) * 10 ^ 70 +
        9861109159079349775730884760568029332668859363077323963101371667532833) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (421 - x)) = _
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
    rw [show 251 = 6 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (422 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (422 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_422 :
    recurrence4Scalar0Main.coeff 422 =
      ((((3614426947826234855478514470800623747755515664446 * 10 ^ 70 +
        3695339767926189585859838436181468024438574643586033385727776182418547) * 10 ^ 70 +
        4322686637137014693174656487073397378046075415816890968385333002115595) * 10 ^ 70 +
        1346695160531283546847366723834877280707743405714544527079921064198072) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (422 - x)) = _
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
    rw [show 251 = 5 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (423 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (423 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_423 :
    recurrence4Scalar0Main.coeff 423 =
      -((((1317582642581352336706809077840773243065691868723 * 10 ^ 70 +
        6967799492645166644350484409956519399838133362265087681530666535351606) * 10 ^ 70 +
        3667881395789481138032552219055356929243772845489449883010884120440464) * 10 ^ 70 +
        9823786636865074445951210597571094556432014481963143445876417711042966) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (423 - x)) = _
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
    rhs
    rw [show 251 = 4 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (424 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (424 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_424 :
    recurrence4Scalar0Main.coeff 424 =
      ((((469059728667898532284110088785540718768664452114 * 10 ^ 70 +
        6425427178386737796077704950323028945528545035840896015600590714250170) * 10 ^ 70 +
        4963688608869876012067918049093049875686956402235998216140131967321857) * 10 ^ 70 +
        9050972416556599088334614223570201239569551316079104652825033343785925) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (424 - x)) = _
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
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 3 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (425 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (425 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_425 :
    recurrence4Scalar0Main.coeff 425 =
      -((((162130963067281793214767689752266189646864678270 * 10 ^ 70 +
        8964334058846000072548488902472748533866853519927279938223787730901585) * 10 ^ 70 +
        7075585953015604247885982692961057847389068216730557333971558680316219) * 10 ^ 70 +
        0141375116279317720367748680625390857266420216915261045823008762788841) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (425 - x)) = _
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
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 2 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (426 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (426 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_426 :
    recurrence4Scalar0Main.coeff 426 =
      ((((54175655122976800490553103256182536723603295231 * 10 ^ 70 +
        9814773003257205508488635164290569738825487530418616158474518519250181) * 10 ^ 70 +
        6434181988621719772319453217526207539633942866005267191759401008013853) * 10 ^ 70 +
        5532145188404631516253188613247994284855007642901469942498274021831021) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (426 - x)) = _
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
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 1 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (427 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (427 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_427 :
    recurrence4Scalar0Main.coeff 427 =
      -((((17440698784760007761553205299190814672040177492 * 10 ^ 70 +
        3456272065844068908366944992985466472650095943164276515862835841840176) * 10 ^ 70 +
        4587469211633135607124479719079930996658260757541883834571543743357877) * 10 ^ 70 +
        9987043516317178573068002830348529492662774373133304376276546808943816) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (427 - x)) = _
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
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (428 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (428 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_428 :
    recurrence4Scalar0Main.coeff 428 =
      ((((5393194851914787178055987405736056812027818934 * 10 ^ 70 +
        3958471973260407878204636049556633830287581541547553723202509739871407) * 10 ^ 70 +
        5767537236545052927222678255767170783364448956291730221423409767251964) * 10 ^ 70 +
        2783701203132059738026578902690244615959525128635046228507268960527890) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (428 - x)) = _
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
    rw [show 283 = 31 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (429 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (429 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_429 :
    recurrence4Scalar0Main.coeff 429 =
      -((((1597028065772894563585510360903736841107353007 * 10 ^ 70 +
        2578856083654423449074527476627030673313544634314563522041516456329165) * 10 ^ 70 +
        7971382788434468712902342104636602792886857800388490901477114482581911) * 10 ^ 70 +
        4201302094665362228987501237395819621855733425713245947187384834909100) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (429 - x)) = _
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
    rw [show 283 = 30 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (430 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (430 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_430 :
    recurrence4Scalar0Main.coeff 430 =
      ((((451177092138232813893939665755757882444255967 * 10 ^ 70 +
        6263477536324367909698094912547833008959099365608103639482317573947257) * 10 ^ 70 +
        0417846630175521606419987525924224708560059948052312318737498847396712) * 10 ^ 70 +
        4903345003449263132529922940478865449295527333667864232227486073033319) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (430 - x)) = _
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
    rw [show 283 = 29 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
