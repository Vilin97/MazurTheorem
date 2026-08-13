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

private theorem recurrence4Scalar0Main_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (431 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (431 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_431 :
    recurrence4Scalar0Main.coeff 431 =
      -((((120985756400612448898241918966269388023544177 * 10 ^ 70 +
        4662278581494059993048973678439568493269499639466528147889461577211097) * 10 ^ 70 +
        4229312824541449729708523051820385061801318059619653446903259786725271) * 10 ^ 70 +
        2385317228459318097564969620294235831593550969613292237495654812763547) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (431 - x)) = _
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
    rw [show 283 = 28 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (432 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (432 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_432 :
    recurrence4Scalar0Main.coeff 432 =
      ((((30557767028647409212167410996067924926612237 * 10 ^ 70 +
        2636623189408979983942455345348701065312929423368558280544541864705999) * 10 ^ 70 +
        9545555211440358986670112521923079610946870096138969513845296303903952) * 10 ^ 70 +
        2915280950073435333001267110279966639970891240091569452149829914866391) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (432 - x)) = _
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
    rw [show 283 = 27 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (433 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (433 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_433 :
    recurrence4Scalar0Main.coeff 433 =
      -((((7176865714575833252379059221873567614167815 * 10 ^ 70 +
        2468995885791404546294761517606435515771105207251800198280150025964870) * 10 ^ 70 +
        3387764538895543893981417871127745914348689279424620782694634418428481) * 10 ^ 70 +
        1982168037633905721687699990189618302311766633572779873368434535315909) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (433 - x)) = _
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
    rw [show 283 = 26 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (434 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (434 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_434 :
    recurrence4Scalar0Main.coeff 434 =
      ((((1530211956596711997321520713571003015278419 * 10 ^ 70 +
        6777681860631142281974699676006673508856118855073838228309968188109486) * 10 ^ 70 +
        9086915975578192722393383328140020605826418829812814227026126504574148) * 10 ^ 70 +
        7185875256959842875798673996913368204430424103976113463723147591404416) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (434 - x)) = _
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
    rw [show 283 = 25 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (435 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (435 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_435 :
    recurrence4Scalar0Main.coeff 435 =
      -((((280678434555424754598227455076597137867806 * 10 ^ 70 +
        6239446640979640448042394947636046330431506368137464135631800022221516) * 10 ^ 70 +
        8307972817091074843344451149291166239116719032536698929201732196395631) * 10 ^ 70 +
        5062454641597746986676816795923721257522527944782313787624768635790169) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (435 - x)) = _
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
    rw [show 283 = 24 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (436 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (436 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_436 :
    recurrence4Scalar0Main.coeff 436 =
      ((((37302050373589897392556640996360113722004 * 10 ^ 70 +
        2396779546724074622337333288061684492346963857644328442086431431633049) * 10 ^ 70 +
        5723691000343855467067679379937596538146029964986113406890186362742438) * 10 ^ 70 +
        8544143416637285652771848931452455572920796742587547797109868463343292) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (436 - x)) = _
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
    rw [show 283 = 23 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (437 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (437 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_437 :
    recurrence4Scalar0Main.coeff 437 =
      ((((56013523658463775727202315192786225514 * 10 ^ 70 +
        7237237937013311989109297840296052243364456964473264303100959763276981) * 10 ^ 70 +
        1738839919800801400543885458626288033736696369141927783351659308836674) * 10 ^ 70 +
        1379961316780581552845856414580116650746443731912769745084778537713355) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (437 - x)) = _
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
    rw [show 283 = 22 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (438 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (438 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_438 :
    recurrence4Scalar0Main.coeff 438 =
      -((((2426905246451285571545307530393778298529 * 10 ^ 70 +
        7835636671415713981733254761979378898391831653427352335150561699549334) * 10 ^ 70 +
        0481619279675433548430823817981893414631956641922334909781909937187113) * 10 ^ 70 +
        6533861772151123092839957485851363516671500799166819912291744174458530) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (438 - x)) = _
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
    rw [show 283 = 21 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (439 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (439 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_439 :
    recurrence4Scalar0Main.coeff 439 =
      ((((1166062663133568486576435041544701714003 * 10 ^ 70 +
        3593619599716695526780525789233447300965874427646051002839607765381833) * 10 ^ 70 +
        5334707293497503890741322599213459642240680016535069061044837620360114) * 10 ^ 70 +
        3475444541519668829821615357514277636273962766692220261639080729170809) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (439 - x)) = _
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
    rw [show 283 = 20 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (440 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (440 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_440 :
    recurrence4Scalar0Main.coeff 440 =
      -((((406402383150994509105440543736521247432 * 10 ^ 70 +
        4670899650771093143084617273161037459378594377201484656258451083070666) * 10 ^ 70 +
        7083251340799553499442309258909023313668223844646318235375737892356149) * 10 ^ 70 +
        6964990110079226734865863446092480561676232152643796231260493915010753) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (440 - x)) = _
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
    rw [show 283 = 19 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (441 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (441 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_441 :
    recurrence4Scalar0Main.coeff 441 =
      ((((121469624748985213751719335468800954609 * 10 ^ 70 +
        3383181517082165205759499168189408347716804558231062592817811637248054) * 10 ^ 70 +
        5822440491356025933310380907313690278010587133142377929576232290427719) * 10 ^ 70 +
        5655412764941814691605151360981983899067827100508333882114645851125942) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (441 - x)) = _
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
    rw [show 283 = 18 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (442 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (442 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_442 :
    recurrence4Scalar0Main.coeff 442 =
      -((((32789762321880366882245737768896169735 * 10 ^ 70 +
        5659575833058413227934390812502968981669866034635492453973167126740907) * 10 ^ 70 +
        6882662638040831727359304365228912714609063909104761536063207030173421) * 10 ^ 70 +
        1499063311114556492617634630086015032309109058119469525729638201070927) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (442 - x)) = _
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
    rw [show 283 = 17 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (443 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (443 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_443 :
    recurrence4Scalar0Main.coeff 443 =
      ((((8174087740398337450313928290988656510 * 10 ^ 70 +
        1564753268607354130207491857239755568856265841615321630393416909509993) * 10 ^ 70 +
        5442240512955836956566073224277007555431450463847155533517337781304067) * 10 ^ 70 +
        3400370450855861049498954539227525334446826160259790373500669629311198) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (443 - x)) = _
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
    rw [show 283 = 16 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (444 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (444 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_444 :
    recurrence4Scalar0Main.coeff 444 =
      -((((1902759058328785621722895420382670667 * 10 ^ 70 +
        1228706147487627513732188992350355819818789037052126691035811591986012) * 10 ^ 70 +
        9277149710557486329484048355229328822660442731329349375564130766703869) * 10 ^ 70 +
        5422374901552792278586633108508931445401653318681300139246366145383197) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (444 - x)) = _
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
    rw [show 283 = 15 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (445 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (445 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_445 :
    recurrence4Scalar0Main.coeff 445 =
      ((((415998523756680062659259509702721985 * 10 ^ 70 +
        2609586504802713319992432453835359986819353257581167824278044266344420) * 10 ^ 70 +
        3106234469417997112916303519464651903470346202978912979547156731714647) * 10 ^ 70 +
        1593875084558470765425448740114880396088975841337393678745276343628762) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (445 - x)) = _
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
    rw [show 283 = 14 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (446 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (446 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_446 :
    recurrence4Scalar0Main.coeff 446 =
      -((((85667782263204375023802371661628909 * 10 ^ 70 +
        2537988822978669796685451880654482068850583747750058448437615009844770) * 10 ^ 70 +
        4925184692312451783762701105711453039665876637038025577177217656468588) * 10 ^ 70 +
        1245979423118491679706874634513182407090275991837669423045184923120188) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (446 - x)) = _
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
    rw [show 283 = 13 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (447 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (447 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_447 :
    recurrence4Scalar0Main.coeff 447 =
      ((((16634522770596241673240172506507066 * 10 ^ 70 +
        4302106392802644990622242781955258983417106627154232404493047931963512) * 10 ^ 70 +
        6126705355614700271133228044921397403154721264805371126263885947875609) * 10 ^ 70 +
        1074203383508974735791565770432790643835761613636201890171880067642238) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (447 - x)) = _
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
    rw [show 283 = 12 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (448 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (448 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_448 :
    recurrence4Scalar0Main.coeff 448 =
      -((((3044531531593215180005004997238186 * 10 ^ 70 +
        3846510656628855501016799151746246666805665257033415852771048956574428) * 10 ^ 70 +
        3738907521871878021415447272148109486792525370276297382275604724197095) * 10 ^ 70 +
        0604560898317744654854279654046013992895299168254424164982527572052468) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (448 - x)) = _
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
    rw [show 283 = 11 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (449 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (449 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_449 :
    recurrence4Scalar0Main.coeff 449 =
      ((((524395713184492196586134116090750 * 10 ^ 70 +
        3256024683302560124374111228021231007091023153186240715438787633213205) * 10 ^ 70 +
        8930624433118955211793410760911288433925702683819973328916590898656793) * 10 ^ 70 +
        3810347069214183159392259645328541444040939706789469823972197961002188) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (449 - x)) = _
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
    rw [show 283 = 10 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (450 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (450 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_450 :
    recurrence4Scalar0Main.coeff 450 =
      -((((84749998365807831284910269039854 * 10 ^ 70 +
        2444831390806731862375270084746639199334567022788725635881958044808968) * 10 ^ 70 +
        9490123498210173500195126401476692428174146565553247121744913431954921) * 10 ^ 70 +
        0475107685879469263752021233887002284943425145469546790768434670876862) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (450 - x)) = _
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
    rw [show 283 = 9 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (451 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (451 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_451 :
    recurrence4Scalar0Main.coeff 451 =
      ((((12789958458162788039787541344640 * 10 ^ 70 +
        6457692445973939159863133110042665498516091359899245198536992311174174) * 10 ^ 70 +
        2497633257469721210358971044545104095535878133082739809703394841119246) * 10 ^ 70 +
        5116621477045215184892396382558556819689081500381225728760052083690426) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (451 - x)) = _
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
    rw [show 283 = 8 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (452 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (452 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_452 :
    recurrence4Scalar0Main.coeff 452 =
      -((((1788436046582445635808267096876 * 10 ^ 70 +
        8687995861167102502871342373369931370998171707345798085228588034526441) * 10 ^ 70 +
        4268188046332058018155498196018520997061959837208569384654830279421870) * 10 ^ 70 +
        8965865891811402974732743160254993845899937819002208750556363854108773) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (452 - x)) = _
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
    rw [show 283 = 7 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (453 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (453 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_453 :
    recurrence4Scalar0Main.coeff 453 =
      ((((228680543307862767966942650518 * 10 ^ 70 +
        5663205836104264536477763961934968180767513182765283495687819398877954) * 10 ^ 70 +
        2718057708261854013397752175940553341410498806995926035344849340943680) * 10 ^ 70 +
        6019898898021527242373994022767943178291989600961191699135500661067771) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (453 - x)) = _
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
    rw [show 283 = 6 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (454 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (454 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_454 :
    recurrence4Scalar0Main.coeff 454 =
      -((((26084138463831003990358046262 * 10 ^ 70 +
        6895649554957403609551591016161924755768003022463461624552474998203531) * 10 ^ 70 +
        7140974913191920988977302136809341002822680720550044307687584353283501) * 10 ^ 70 +
        8129019021759499960482808642620554591294220042340018899172288317758272) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (454 - x)) = _
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
    rw [show 283 = 5 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (455 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (455 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_455 :
    recurrence4Scalar0Main.coeff 455 =
      ((((2510187774707568465383057577 * 10 ^ 70 +
        9123024693963813421230575105832473118945237386474383748545796438531894) * 10 ^ 70 +
        9610580799548800880380893539889847593394783812396723708268621886369843) * 10 ^ 70 +
        2150197891840080746405058369055221213696425320152151218417711329545755) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (455 - x)) = _
  rw [show 456 = 109 +
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
  rw [recurrence4Scalar0Main_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
