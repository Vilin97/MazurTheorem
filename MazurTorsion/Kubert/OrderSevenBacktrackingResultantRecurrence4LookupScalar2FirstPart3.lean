/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

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
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95

attribute [local simp]
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
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
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_270

attribute [local simp]
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
  recurrence4B3A4_coeff_329
  recurrence4B3A4_coeff_330
  recurrence4B3A4_coeff_331
  recurrence4B3A4_coeff_332
  recurrence4B3A4_coeff_333
  recurrence4B3A4_coeff_334

attribute [local simp]
  recurrence4B3A4_coeff_335
  recurrence4B3A4_coeff_336
  recurrence4B3A4_coeff_337
  recurrence4B3A4_coeff_338
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar2First_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (383 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (383 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_383 :
    recurrence4Scalar2First.coeff 383 =
      ((((135616457857193956261577189620289437579155731058907720763479572 * 10 ^ 70 +
        8316624088303310937667262470019848216278741653841560192589167302735535) * 10 ^ 70 +
        6571024617479239527548455694554589689048199852403129170976784284641931) * 10 ^ 70 +
        2220829568029488385789930565842573876066336381603131618146126143431305) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (383 - x)) = _
  rw [show 384 = 41 +
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
  rw [recurrence4Scalar2First_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_383_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (384 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (384 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_384 :
    recurrence4Scalar2First.coeff 384 =
      -((((79173122660287896025705187191683868933897413437649212331703735 * 10 ^ 70 +
        6957828420989188045733225144523813825416973203421400329875189179430896) * 10 ^ 70 +
        7008251365516085085510194471622197354478099468795477259781712748417458) * 10 ^ 70 +
        3247514325006805526760582061472587768411166286044343919396064111377630) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (384 - x)) = _
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
    rw [show 215 = 3 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_384_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (385 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (385 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_385 :
    recurrence4Scalar2First.coeff 385 =
      ((((37181561195911405928780068329006439862366895499303940727563909 * 10 ^ 70 +
        9175610119483711980219496186403843922816760995351220676110484828619566) * 10 ^ 70 +
        7401476673349140199032482241338476964767191528542616543617449359774535) * 10 ^ 70 +
        5943264692926825435547904342800281925027870337152571869159731330247337) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (385 - x)) = _
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
    rw [show 215 = 2 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_385_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (386 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (386 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_386 :
    recurrence4Scalar2First.coeff 386 =
      -((((15539894517158065019938870035347404141180953771098179246961947 * 10 ^ 70 +
        8618961363152139609377933946946649381404304279751483845164785786258121) * 10 ^ 70 +
        9555320070524725844925940735022482941883509535188022760540635404358671) * 10 ^ 70 +
        7691863660111639311352276327306746970444014010706501486917704749034391) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (386 - x)) = _
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
    rw [show 215 = 1 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_386_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (387 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (387 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_387 :
    recurrence4Scalar2First.coeff 387 =
      ((((6000784182117445792051081034237059373800747688190600423956045 * 10 ^ 70 +
        4644696782141007087139704097717796665320881836352084753430808613597763) * 10 ^ 70 +
        1406380363161602599165584715858414502340604621992882679243907925907772) * 10 ^ 70 +
        8747158327774143066805639580310341081466792062442405012582231628800726) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (387 - x)) = _
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
  rw [recurrence4Scalar2First_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_387_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (388 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (388 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_388 :
    recurrence4Scalar2First.coeff 388 =
      -((((2179934629402585939254862903758721571028106497323480503777295 * 10 ^ 70 +
        1349802986529894015490694823223049701395621987151827925726757407939309) * 10 ^ 70 +
        9919725121707775423449402413072235196685392677708604933019777729834732) * 10 ^ 70 +
        1349576119190736725582159900039377787724881950510239755174502697458232) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (388 - x)) = _
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
    rw [show 247 = 31 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_388_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (389 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (389 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_389 :
    recurrence4Scalar2First.coeff 389 =
      ((((752539304642032417517327906726154174397040478249984187236450 * 10 ^ 70 +
        7954644299277026103102202934003293757500789112641175060925507041159933) * 10 ^ 70 +
        3184065503344582265229912503183456201970282346878935678581292096248401) * 10 ^ 70 +
        1077476074310247115587637916767562489671045803813417442709793581557144) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (389 - x)) = _
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
    rw [show 247 = 30 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_389_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (390 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (390 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_390 :
    recurrence4Scalar2First.coeff 390 =
      -((((248356352069774752591844442935761063415222095513067375380767 * 10 ^ 70 +
        5134046037002656597852396395063666393928835787018310283764327189546860) * 10 ^ 70 +
        8069583928076007287474710925748572353743900084703894544749634203232841) * 10 ^ 70 +
        6941933786796042687113739706102762288867004987983428773258998200488408) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (390 - x)) = _
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
    rw [show 247 = 29 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_390_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (391 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (391 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_391 :
    recurrence4Scalar2First.coeff 391 =
      ((((78604971495677368163627533771127376721056111113289216731886 * 10 ^ 70 +
        0791858041097290719293505525771288042530679568818766048185264872509482) * 10 ^ 70 +
        4761289955272806329358541148078304395885215137048459219638938206225894) * 10 ^ 70 +
        1660782787445558700725482037654139993690857853229370694335237705242473) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (391 - x)) = _
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
    rw [show 247 = 28 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_391_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (392 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (392 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_392 :
    recurrence4Scalar2First.coeff 392 =
      -((((23855933142391132961231635597787202336037308734272373396974 * 10 ^ 70 +
        5542662693115849734445468249291733097962625345546640723070307921524855) * 10 ^ 70 +
        8866754543151905615748767021686122872432160230685140475565440290493533) * 10 ^ 70 +
        7672548176219164260639559258877436873324491539655984733319380345369779) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (392 - x)) = _
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
    rw [show 247 = 27 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_392_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (393 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (393 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_393 :
    recurrence4Scalar2First.coeff 393 =
      ((((6903308638250149348211206145483807785549721753819213861356 * 10 ^ 70 +
        8361327459763317779315411526687785444137409875217946578152579576823253) * 10 ^ 70 +
        8110392116049824797588867480925739133109970283531255230780552741933551) * 10 ^ 70 +
        1309112769252606150480174450879922714239203470663592982690165801804954) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (393 - x)) = _
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
    rw [show 247 = 26 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_393_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (394 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (394 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_394 :
    recurrence4Scalar2First.coeff 394 =
      -((((1872883017524018623920117873483318452391461261185807523793 * 10 ^ 70 +
        7345341662214371077625894633987279581357423644510548783593085813905570) * 10 ^ 70 +
        9817077494364339859034041202739926339920543556636028740565291370028074) * 10 ^ 70 +
        3488669178803465727067684008498525047404982051321389619194631120080466) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (394 - x)) = _
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
    rw [show 247 = 25 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_394_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (395 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (395 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_395 :
    recurrence4Scalar2First.coeff 395 =
      ((((455942797134693070062262917479081889788886124422938868447 * 10 ^ 70 +
        2486298871977122553016611095632240866702217538088935641350504638819940) * 10 ^ 70 +
        0086734329882670196337264297418519273633091508972644275078958308120451) * 10 ^ 70 +
        3263597663762936707370955909276354773358071751141314635564303163864234) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (395 - x)) = _
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
    rw [show 247 = 24 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_395_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (396 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (396 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_396 :
    recurrence4Scalar2First.coeff 396 =
      -((((86914115107118167017364099173001912114513318900910986045 * 10 ^ 70 +
        4608996496007803711307257452841776750782881175109258078862755018689346) * 10 ^ 70 +
        0851645058934561456977604754243454802854882753197765912285540267309422) * 10 ^ 70 +
        0290963748406471438348413414182330288952756861256015801054088073180998) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (396 - x)) = _
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
    rw [show 247 = 23 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_396_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (397 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (397 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_397 :
    recurrence4Scalar2First.coeff 397 =
      ((((4225111588748112650555523061926608406797916581077482792 * 10 ^ 70 +
        9634153810936646712529329727018542293337066322380738016916881727942726) * 10 ^ 70 +
        4241266210347245265975708773589166497978309125677188967078792521183937) * 10 ^ 70 +
        7690505385280474558615529353283107633013666954103185540312039980359236) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (397 - x)) = _
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
    rw [show 247 = 22 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (398 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (398 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_398 :
    recurrence4Scalar2First.coeff 398 =
      ((((7745784730926954365075113553599791607658698129657697668 * 10 ^ 70 +
        9395345285804524832763792002473236914589382526153481733881662224569337) * 10 ^ 70 +
        5461805717429727845536657888358206029491388051008818415013201587405342) * 10 ^ 70 +
        2311396465032437647798278321028141292499143439221164132159916060902699) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (398 - x)) = _
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
    rw [show 247 = 21 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (399 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (399 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_399 :
    recurrence4Scalar2First.coeff 399 =
      -((((5816721308882541729578607351907988621585318894672659979 * 10 ^ 70 +
        3789619808518447415942345445457330331566947850228050038266175854741037) * 10 ^ 70 +
        0963138922777312930347822299556415870092678254433369776652506738680689) * 10 ^ 70 +
        8425755565177369186677301993562997224135355642710791383899006868542720) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (399 - x)) = _
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
    rw [show 247 = 20 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (400 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (400 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_400 :
    recurrence4Scalar2First.coeff 400 =
      ((((3007018040720954859493289655783586020719107381399501969 * 10 ^ 70 +
        9724155393260224367030617048178918171302550967596011102415771887379095) * 10 ^ 70 +
        7017989155782927415539272525812673736539278256588089702225636293013721) * 10 ^ 70 +
        0929182740754133365915298405889118480196730133428695464242479813301186) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (400 - x)) = _
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
    rw [show 247 = 19 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (401 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (401 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_401 :
    recurrence4Scalar2First.coeff 401 =
      -((((1322179473080132783338495067996795255585376821412325057 * 10 ^ 70 +
        0224715794479856842525024269156692503984739278619506888994711994573651) * 10 ^ 70 +
        6676179371400979238689096153280428518943150828149680381548590012902118) * 10 ^ 70 +
        2581258737362673953741523857389856627368763374552323180749057961589415) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (401 - x)) = _
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
    rw [show 247 = 18 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (402 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (402 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_402 :
    recurrence4Scalar2First.coeff 402 =
      ((((522927902746805100823393832475744194526838186940332142 * 10 ^ 70 +
        9611211169005490402059327588834199860242792359224729932868870267521934) * 10 ^ 70 +
        1521830343673722796621184400226792796534851663417033040776956644517349) * 10 ^ 70 +
        5431373105572043978825447378225330131790865520790577213020081020678788) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (402 - x)) = _
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
    rw [show 247 = 17 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (403 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (403 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_403 :
    recurrence4Scalar2First.coeff 403 =
      -((((189763086514037255729865763603911357806460981019043579 * 10 ^ 70 +
        8588184162984164920341235444395445601569654965383972615422199100060277) * 10 ^ 70 +
        3984215776234105256915761809891347969453060710119130462959553850256946) * 10 ^ 70 +
        1547276306054039656011816662125499782889356385283808926063958649721939) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (403 - x)) = _
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
    rw [show 247 = 16 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (404 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (404 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_404 :
    recurrence4Scalar2First.coeff 404 =
      ((((63523220192420284693807756361097202614122566087625487 * 10 ^ 70 +
        0803902828297264664089728818854126066024591476154112483610603560136802) * 10 ^ 70 +
        9157469099048844547778957584932564047436771265459555851677255146590850) * 10 ^ 70 +
        6782791903614427109337775983684124066082866251621382081999552422378479) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (404 - x)) = _
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
    rw [show 247 = 15 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (405 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (405 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_405 :
    recurrence4Scalar2First.coeff 405 =
      -((((19526375866868996658646221248099365022439959011889084 * 10 ^ 70 +
        0174059866705456825391811728742717877323886912698939559007784253794074) * 10 ^ 70 +
        2927172920005189152808475869661132124740664115085299031122747045028743) * 10 ^ 70 +
        4616243887964490124675510354834928742118436290620799489678079125149904) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (405 - x)) = _
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
    rw [show 247 = 14 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (406 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (406 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_406 :
    recurrence4Scalar2First.coeff 406 =
      ((((5415319604841330440643607767731612662910168651556909 * 10 ^ 70 +
        3537431743307160810654738112933050315350321714004171915512853375987807) * 10 ^ 70 +
        7044414482204661992406802025974815773759567303399181673592832321081067) * 10 ^ 70 +
        6483755838659573533979417609938271570282432716400463087520171862712296) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (406 - x)) = _
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
    rw [show 247 = 13 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (407 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (407 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_407 :
    recurrence4Scalar2First.coeff 407 =
      -((((1292510409869921813748113039788994741362945295758951 * 10 ^ 70 +
        5323035723909968425577810872463974382473425494386672873093708720370620) * 10 ^ 70 +
        9496153085346443497635463209347875456876699373606138991424389273425220) * 10 ^ 70 +
        2644110767758194247465368014852014064728871123416450078498288563883091) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (407 - x)) = _
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
    rw [show 247 = 12 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (408 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (408 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_408 :
    recurrence4Scalar2First.coeff 408 =
      ((((226654478519080280237904891634659688996074170058626 * 10 ^ 70 +
        1109876924692927633961170021463746777127188357043612849958012715212015) * 10 ^ 70 +
        8184351387234279798159961272257860489425335061033270900414626380976430) * 10 ^ 70 +
        7078408170009838081614585013557782911335676266163599450867333212865756) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (408 - x)) = _
  rw [show 409 = 66 +
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
    rw [show 247 = 11 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (409 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (409 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_409 :
    recurrence4Scalar2First.coeff 409 =
      -((((2381111605416347668355817981086654390570351656434 * 10 ^ 70 +
        5478044114287288735121952675344586821546363732822483685821232984763574) * 10 ^ 70 +
        6168839849030289764970911648764389224493731988355530285901520882645821) * 10 ^ 70 +
        2544177010791527664350689198482864921439725600317789636197911047943173) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (409 - x)) = _
  rw [show 410 = 67 +
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
    rw [show 247 = 10 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (410 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (410 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_410 :
    recurrence4Scalar2First.coeff 410 =
      -((((23424987328999430695680011336332883297145536238621 * 10 ^ 70 +
        8276923983361948381848823509930625855090453609038468969535471754575746) * 10 ^ 70 +
        4032195645499931841689416628030069081772066653747949000754211158789023) * 10 ^ 70 +
        0140857286193297561628531969362784276600379677057776423474629815579582) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (410 - x)) = _
  rw [show 411 = 68 +
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
    rw [show 247 = 9 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (411 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (411 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_411 :
    recurrence4Scalar2First.coeff 411 =
      ((((15330078845519623170024962400788863673325893134978 * 10 ^ 70 +
        5074989517068935188504361042086260358909484210401531021838741394110501) * 10 ^ 70 +
        6622536000680310070715557054294647604993370241101325168473323494645563) * 10 ^ 70 +
        0705531850830010839758244092623150732636860263863600064929587430260266) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (411 - x)) = _
  rw [show 412 = 69 +
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
    rw [show 247 = 8 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (412 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (412 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_412 :
    recurrence4Scalar2First.coeff 412 =
      -((((7329140162754572849557185354305248315484304241881 * 10 ^ 70 +
        1144638198332021400455500133505356972149507511273100676265389108112842) * 10 ^ 70 +
        6178546627045622970009613710722856602283600535199903627833062118491279) * 10 ^ 70 +
        6708830950401123784115660288557177615346313151251980559470347694795483) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (412 - x)) = _
  rw [show 413 = 70 +
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
    rw [show 247 = 7 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (413 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (413 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_413 :
    recurrence4Scalar2First.coeff 413 =
      ((((3072404423109678147070418974388796698936725578872 * 10 ^ 70 +
        2913412866447623581644985492403081849740725954463006132359544741945332) * 10 ^ 70 +
        5046809035994817349947767330373175317059602216897158932311726330464238) * 10 ^ 70 +
        3848669363831008793150117965000721216593415373909042411149684903579442) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (413 - x)) = _
  rw [show 414 = 71 +
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
    rw [show 247 = 6 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (414 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (414 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_414 :
    recurrence4Scalar2First.coeff 414 =
      -((((1197745735514715367554280042560624106959199193425 * 10 ^ 70 +
        1679233061862108857391957560432346789849313109156054720319811295496703) * 10 ^ 70 +
        1168261294889029524690888205565208455198329572392494440916736655744617) * 10 ^ 70 +
        7685015605467884379711453802392956236877273016915140048925722754896608) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (414 - x)) = _
  rw [show 415 = 72 +
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
    rw [show 247 = 5 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (415 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (415 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_415 :
    recurrence4Scalar2First.coeff 415 =
      ((((446174406849393552016798196171705692680469105032 * 10 ^ 70 +
        0084842337283021645431229159515763375312792714356398355133474748323366) * 10 ^ 70 +
        4830192669775388939023690008469840386851820638877692161166335615692124) * 10 ^ 70 +
        6707342849117777582621510501495366730697003682027932853402190145982798) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (415 - x)) = _
  rw [show 416 = 73 +
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
    rw [show 247 = 4 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (416 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (416 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_416 :
    recurrence4Scalar2First.coeff 416 =
      -((((161048175138657425605974706109087460209922197274 * 10 ^ 70 +
        8831382697126516721587364046005486250603815730477376739028494815885751) * 10 ^ 70 +
        1128897853635050274731301657338177913907238966502774465844628509366368) * 10 ^ 70 +
        9483690885696480129144323538987868647073461009174978151437699737455857) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (416 - x)) = _
  rw [show 417 = 74 +
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
    rw [show 247 = 3 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (417 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (417 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_417 :
    recurrence4Scalar2First.coeff 417 =
      ((((56681460615974682667872280417553604245539264232 * 10 ^ 70 +
        5571298477227078925714305743841724323832461476079249634202924053958893) * 10 ^ 70 +
        4277874927257237878349979717904634768227793531359115614919690371003669) * 10 ^ 70 +
        0688616478166237969510819945422558470919374791945852831458832876522289) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (417 - x)) = _
  rw [show 418 = 75 +
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
    rw [show 247 = 2 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (418 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (418 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_418 :
    recurrence4Scalar2First.coeff 418 =
      -((((19468827442444534025505500733581407838782376579 * 10 ^ 70 +
        9691564629505967310969246269766354232642830441571843744311824091736567) * 10 ^ 70 +
        7622445491813740765734463514703648428759841244489880015246399777045400) * 10 ^ 70 +
        8478903468854981770352157153807944345704643400763939368956435728536696) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (418 - x)) = _
  rw [show 419 = 76 +
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
    rw [show 247 = 1 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (419 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (419 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_419 :
    recurrence4Scalar2First.coeff 419 =
      ((((6505992896104330651643024141957340792528517962 * 10 ^ 70 +
        9970834760661544746203567946102658986374505343475928378163510087124897) * 10 ^ 70 +
        3196811576720696064681267772111558791130525586897518996466049626188616) * 10 ^ 70 +
        4263045435625337702359078904629597235166854803318675588366185533318439) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (419 - x)) = _
  rw [show 420 = 77 +
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
  rw [recurrence4Scalar2First_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (420 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (420 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_420 :
    recurrence4Scalar2First.coeff 420 =
      -((((2102769677892434060424217872466061385019422260 * 10 ^ 70 +
        2293409947639373501015616995907099521058411817481113976941106294460670) * 10 ^ 70 +
        7113066010527639353970950242528115637087026902981505853677851255137929) * 10 ^ 70 +
        4169812480472205373778117540239993584543259970666992015005484721398785) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (420 - x)) = _
  rw [show 421 = 78 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 31 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (421 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (421 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_421 :
    recurrence4Scalar2First.coeff 421 =
      ((((652022527245224719321272414265660670777186726 * 10 ^ 70 +
        0160028129805543580213620584469431148222814552909554592129504506935855) * 10 ^ 70 +
        0282039726490068236660695114130863574238027611437113288495014478500314) * 10 ^ 70 +
        1516956642600287752875641412864351773156094668378307393927951715479760) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (421 - x)) = _
  rw [show 422 = 79 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 30 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (422 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (422 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_422 :
    recurrence4Scalar2First.coeff 422 =
      -((((191966024677735208842476953890411156994752433 * 10 ^ 70 +
        8519276797126024685844109017794290923983706953942207313730499244788943) * 10 ^ 70 +
        1299570410518328976173961888016754457787058473586948884237709054771830) * 10 ^ 70 +
        1384617472090722807935093226065283144769273121615396520161055903889559) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (422 - x)) = _
  rw [show 423 = 80 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 29 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (423 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (423 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_423 :
    recurrence4Scalar2First.coeff 423 =
      ((((52911192621921228229321511436151879903151923 * 10 ^ 70 +
        8495813397094201882668617463855421832618405711173361231606819075261250) * 10 ^ 70 +
        5842001691845853460650163729667655721549189798656129327414475633430899) * 10 ^ 70 +
        2475956513352893245808063540825162315872083436773391637887190010667291) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (423 - x)) = _
  rw [show 424 = 81 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 28 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (424 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (424 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_424 :
    recurrence4Scalar2First.coeff 424 =
      -((((13353330321217075593232239933260566083391673 * 10 ^ 70 +
        2724883957506803835158682398608345102040534797865162967479021457988890) * 10 ^ 70 +
        0398203094483958988826489009944551531083001112524543256571343920748837) * 10 ^ 70 +
        5522130298990081052390754926568649169033631810700088302188983733196684) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (424 - x)) = _
  rw [show 425 = 82 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 27 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (425 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (425 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_425 :
    recurrence4Scalar2First.coeff 425 =
      ((((2955230978275680595840124130872343308777757 * 10 ^ 70 +
        0056562473399272525911020458537967419975897085064155067158174088581824) * 10 ^ 70 +
        1142055044009767023332744798480912732759276390649449979684627147525332) * 10 ^ 70 +
        3286787415823053735550911915667099429947020200926664043397208311628166) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (425 - x)) = _
  rw [show 426 = 83 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 26 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (426 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (426 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_426 :
    recurrence4Scalar2First.coeff 426 =
      -((((510616753314877624603294390643450990112871 * 10 ^ 70 +
        5714645540288662258254716671743770201727332101145964091964561910650876) * 10 ^ 70 +
        5276312080558165034162043049501581650812801588960447757925789961025059) * 10 ^ 70 +
        9479829611553763416856144464639647921063102421643699602053107516859970) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (426 - x)) = _
  rw [show 427 = 84 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 25 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (427 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (427 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_427 :
    recurrence4Scalar2First.coeff 427 =
      ((((33991949828143054664613643130479745301788 * 10 ^ 70 +
        3015343007798954170446937058941557913992785133061953757886061234124345) * 10 ^ 70 +
        3887471674260816957040661503522721949926940684060356014681863926897984) * 10 ^ 70 +
        9938633841650988511507577259566630246133041470289700675449880221975530) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (427 - x)) = _
  rw [show 428 = 85 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 24 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (428 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (428 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_428 :
    recurrence4Scalar2First.coeff 428 =
      ((((23530893906306241713880673098506043695258 * 10 ^ 70 +
        5496466463368768745491581687874097173603760750182321385262310720499174) * 10 ^ 70 +
        7568935036111222706450115883546747669042497545884173556680693150866879) * 10 ^ 70 +
        9925640032723529828114599571542367281072109159461766999370305242780071) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (428 - x)) = _
  rw [show 429 = 86 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 23 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (429 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (429 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_429 :
    recurrence4Scalar2First.coeff 429 =
      -((((15487758508387946551964232793135261087488 * 10 ^ 70 +
        2405977860027208488820541408383073531691108312394657882905219017411531) * 10 ^ 70 +
        0851659283917630832370450084746445327954762635367401123366964427790864) * 10 ^ 70 +
        4909259527924028197466914799996843846699342922347333734638417340121460) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (429 - x)) = _
  rw [show 430 = 87 +
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
  rw [recurrence4Scalar2First_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (430 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (430 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_430 :
    recurrence4Scalar2First.coeff 430 =
      ((((6435210887059936841857893855188700046478 * 10 ^ 70 +
        1740119340199996941017022564807230833766314979513585513761719815354685) * 10 ^ 70 +
        4871365838956691231800698528018465798805724238921785275350418227997518) * 10 ^ 70 +
        7466669457826898870965618182496049727148744035425637398397437990514621) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (430 - x)) = _
  rw [show 431 = 88 +
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
  rw [recurrence4Scalar2First_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (431 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (431 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_431 :
    recurrence4Scalar2First.coeff 431 =
      -((((2214270365147098204990899888811893851086 * 10 ^ 70 +
        9180056699204217578274086015394477373756908622041462581888330876134515) * 10 ^ 70 +
        2877310804635659022193941700421832568948311595929348979678123630119523) * 10 ^ 70 +
        4796551805412133913102738308616914756784680672542624271740436259238074) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (431 - x)) = _
  rw [show 432 = 89 +
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
  rw [recurrence4Scalar2First_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (432 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (432 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_432 :
    recurrence4Scalar2First.coeff 432 =
      ((((676383101991886191579102858092855860305 * 10 ^ 70 +
        5218036713139961403897399529373270481264844813961331174721835796993882) * 10 ^ 70 +
        1474175632794868793502970704715605956187742962729575354767528138893746) * 10 ^ 70 +
        0013977872850663104682263858619155504681967773939437390167017718391170) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (432 - x)) = _
  rw [show 433 = 90 +
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
  rw [recurrence4Scalar2First_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (433 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (433 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_433 :
    recurrence4Scalar2First.coeff 433 =
      -((((188534758505717429220014765510930984387 * 10 ^ 70 +
        2729604434527615399555533306948899652149452209071783305546896814578199) * 10 ^ 70 +
        1981273790073210769078655396283437870813567962527857029062152438484267) * 10 ^ 70 +
        6970150960014632295263614822917681266473023753145600216040033128759290) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (433 - x)) = _
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
    rw [show 279 = 18 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (434 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (434 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_434 :
    recurrence4Scalar2First.coeff 434 =
      ((((48565633339095309489232503206967765655 * 10 ^ 70 +
        1348254778773747147273186925077889398696688971975248247220391095023660) * 10 ^ 70 +
        3352475821178714796880200086579655717696185273183155711423906972684873) * 10 ^ 70 +
        4847566665751175349556279127179798197066447006044060766692818455732266) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (434 - x)) = _
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
    rw [show 279 = 17 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (435 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (435 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_435 :
    recurrence4Scalar2First.coeff 435 =
      -((((11627363739601584751683240876862981126 * 10 ^ 70 +
        3856518576497487981195996221736723159692030204272059795232977179899597) * 10 ^ 70 +
        1889310606409325124636866851368552399621292167307704287541627548910525) * 10 ^ 70 +
        7702313865920225622766924714942334981052878716709914362828768907134087) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (435 - x)) = _
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
    rw [show 279 = 16 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (436 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (436 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_436 :
    recurrence4Scalar2First.coeff 436 =
      ((((2591257193289847016761823905721825260 * 10 ^ 70 +
        6952970765134651457601034952476984056812028991808675004128899623094497) * 10 ^ 70 +
        5695142588782511472110925956403700711315072379136487343726101250513940) * 10 ^ 70 +
        5936266274110880553677726758781370096204494580758472891803023964611931) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (436 - x)) = _
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
    rw [show 279 = 15 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (437 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (437 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_437 :
    recurrence4Scalar2First.coeff 437 =
      -((((536612946574311824367597869669761707 * 10 ^ 70 +
        5237710437258753514938855285747937127649874718829630056423743947560605) * 10 ^ 70 +
        8697524321472250790706669595902576354804571851047738024280396369618651) * 10 ^ 70 +
        7906432316465453774967683431714753910001628364190023248419679739415573) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (437 - x)) = _
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
    rw [show 279 = 14 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (438 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (438 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_438 :
    recurrence4Scalar2First.coeff 438 =
      ((((102727413938207782265861741132680349 * 10 ^ 70 +
        1839547821880456676960311639214492408439201981885047229334535450969843) * 10 ^ 70 +
        4953089531551241360054789135111366591329941872760539352740252393989608) * 10 ^ 70 +
        0954386684055383546705684989958194984162665603050206013157597477238284) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (438 - x)) = _
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
    rw [show 279 = 13 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (439 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (439 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_439 :
    recurrence4Scalar2First.coeff 439 =
      -((((17999661421802194191250428084929531 * 10 ^ 70 +
        1687762463101886195191154489353721379424625607931421129752157266362712) * 10 ^ 70 +
        1256746922934257163707341382270036164508519993653063626499279023349240) * 10 ^ 70 +
        2476615617461095897444429489348855489154566814157556934892050824729200) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (439 - x)) = _
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
    rw [show 279 = 12 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (440 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (440 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_440 :
    recurrence4Scalar2First.coeff 440 =
      ((((2834007754837637552791675607581140 * 10 ^ 70 +
        8921276024158762087109413724135272477950930230958463129649250084406392) * 10 ^ 70 +
        2377535540219414374000200415492031172845199502533477069370056341577347) * 10 ^ 70 +
        8241498642588577487889838263884814521317569024100967522058617409236272) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (440 - x)) = _
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
    rw [show 279 = 11 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (441 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (441 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_441 :
    recurrence4Scalar2First.coeff 441 =
      -((((386268944396902812885235739711431 * 10 ^ 70 +
        9332483701762848004891440434990110089472327852337265420929939781172270) * 10 ^ 70 +
        2201119803154843581327588627568070991084852308078244160588821400275697) * 10 ^ 70 +
        5624997638532826099480306150321224515467710642911076534136043798338077) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (441 - x)) = _
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
    rw [show 279 = 10 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (442 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (442 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_442 :
    recurrence4Scalar2First.coeff 442 =
      ((((41435036902683792956951866477912 * 10 ^ 70 +
        9754672119405950146493099378802865978879411670044541224561773748480060) * 10 ^ 70 +
        4557439803045721588957118978676416354570866442877173815277748261673318) * 10 ^ 70 +
        2821055384959202800448533495395575078395130436984557554405946366775350) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (442 - x)) = _
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
    rw [show 279 = 9 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (443 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (443 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_443 :
    recurrence4Scalar2First.coeff 443 =
      -((((2239990966729417783179819027268 * 10 ^ 70 +
        6987978727604738114668256563191080652860541316115792841936835991069020) * 10 ^ 70 +
        8150174199475033772084759876217295178458002871877655042334825418921165) * 10 ^ 70 +
        4048302723784133178030233439473628922292632253009995093548134370096045) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (443 - x)) = _
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
    rw [show 279 = 8 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (444 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (444 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_444 :
    recurrence4Scalar2First.coeff 444 =
      -((((395869419034430022630683245793 * 10 ^ 70 +
        8784805107723273176546840321107076679301486607201506784182393895071502) * 10 ^ 70 +
        0974353264725998427219267544923153698924937081487124217239485031055282) * 10 ^ 70 +
        7318227873311389624495118444817423967079614384746480109790757184917508) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (444 - x)) = _
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
    rw [show 279 = 7 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (445 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (445 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_445 :
    recurrence4Scalar2First.coeff 445 =
      ((((166053849261241301862503857199 * 10 ^ 70 +
        1976648358066068116062038114471249650314502865410190693944863017897844) * 10 ^ 70 +
        6742810318691367790798063786720825780678449001155489585693505455227011) * 10 ^ 70 +
        7393535908314406821974053620058498876114381524758345828305240903128982) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (445 - x)) = _
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
    rw [show 279 = 6 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (446 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (446 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_446 :
    recurrence4Scalar2First.coeff 446 =
      -((((36271279263247753093498120458 * 10 ^ 70 +
        5663181508510766186222041991540667318906498836524609996320095809799850) * 10 ^ 70 +
        8277598681454177947719258937753520372231292219525795920785698660254977) * 10 ^ 70 +
        3858283073371232211559318077047252743283053122535073952661367378398499) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (446 - x)) = _
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
    rw [show 279 = 5 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (447 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (447 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_447 :
    recurrence4Scalar2First.coeff 447 =
      ((((5933606125707917095557264946 * 10 ^ 70 +
        1947435596680655429496470778710740652625575496012331847234518757930676) * 10 ^ 70 +
        5706310817096035061083881068503997317070589340362983236366512442558549) * 10 ^ 70 +
        3909136306926302767194678638032113831439483876664873614069505730359936) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (447 - x)) = _
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
    rw [show 279 = 4 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (448 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (448 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_448 :
    recurrence4Scalar2First.coeff 448 =
      -((((753420914061008303224847803 * 10 ^ 70 +
        4750516069019141952675338769687564148598629362322131716072691651310057) * 10 ^ 70 +
        3358484095065734323259868186893393648783445363267856192639909158671864) * 10 ^ 70 +
        9489282061522726349834274119191028690740172769386886379500263322582226) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (448 - x)) = _
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
    rw [show 279 = 3 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (449 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (449 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_449 :
    recurrence4Scalar2First.coeff 449 =
      ((((66564159965626282528068669 * 10 ^ 70 +
        6200605749215526787571904570117259001921855311805593958403033990149303) * 10 ^ 70 +
        4776770095119053782136384438235229328557209048701556671622228058825641) * 10 ^ 70 +
        1501338472144315118803352760756726987586491577508340506109984025201772) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (449 - x)) = _
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
    rw [show 279 = 2 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (450 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (450 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_450 :
    recurrence4Scalar2First.coeff 450 =
      -((((1280420764325721788381431 * 10 ^ 70 +
        7116568692044344980981226843636491454199086962850408113337745113495209) * 10 ^ 70 +
        7468205400664004813719186173496104964246033789987604186726192502562397) * 10 ^ 70 +
        6786065456308516471877389649705068271962807736028860523441088731022291) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (450 - x)) = _
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
    rw [show 279 = 1 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (451 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (451 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_451 :
    recurrence4Scalar2First.coeff 451 =
      -((((968409607513760263095889 * 10 ^ 70 +
        7261626448801868824285874469675446853743204685406675239076370031640350) * 10 ^ 70 +
        3780342278101333978177592862653005389617951932852289815388915694429211) * 10 ^ 70 +
        7054046811155275565958861410588453905608925748492670850460027745274431) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (451 - x)) = _
  rw [show 452 = 109 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (452 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (452 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_452 :
    recurrence4Scalar2First.coeff 452 =
      ((((247833171114124002539925 * 10 ^ 70 +
        4814869450805770433164334026946346000525882158550392630181188981181011) * 10 ^ 70 +
        1384110693440250012174349033188289481036189088196123261462140425486374) * 10 ^ 70 +
        4223290882566767873926518181381256643328608592736706080290971073984909) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (452 - x)) = _
  rw [show 453 = 110 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 31 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (453 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (453 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_453 :
    recurrence4Scalar2First.coeff 453 =
      -((((38860406983719642009157 * 10 ^ 70 +
        9503009985109929741075887084316026347420840838474764217799854960053829) * 10 ^ 70 +
        9638779095961581615775643675443559447712765663671601982164797350687489) * 10 ^ 70 +
        2504314730306588855758975014140268546978774943238156408542946272385878) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (453 - x)) = _
  rw [show 454 = 111 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 30 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (454 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (454 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_454 :
    recurrence4Scalar2First.coeff 454 =
      ((((4364367042153621048784 * 10 ^ 70 +
        5167089540108647304405201838936396230473840597869971782300119662767892) * 10 ^ 70 +
        3662465320681655053773047395896273729555741822888158791739454347027415) * 10 ^ 70 +
        8180311682716333972161356989382109871528661205751374542501158149213599) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (454 - x)) = _
  rw [show 455 = 112 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 29 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (455 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (455 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_455 :
    recurrence4Scalar2First.coeff 455 =
      -((((309257747135081411468 * 10 ^ 70 +
        8060658589531275016333218032739213498998117367690988309147277500168491) * 10 ^ 70 +
        8977055679370920598406548591844966138323977952360535580836008388576372) * 10 ^ 70 +
        7086911212350339670603722313756900136747959890486178748677467034374206) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (455 - x)) = _
  rw [show 456 = 113 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 28 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (456 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (456 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_456 :
    recurrence4Scalar2First.coeff 456 =
      -((((2375638847984565318 * 10 ^ 70 +
        0228349904837312460184547339877880710313770697470901236636263889406687) * 10 ^ 70 +
        2405953784870032639554167810896119261059219256998275592980479677165733) * 10 ^ 70 +
        9177226212859550590284095147914915746448061690834607099864485939648635) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (456 - x)) = _
  rw [show 457 = 114 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 27 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (457 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (457 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_457 :
    recurrence4Scalar2First.coeff 457 =
      ((((4997289860282836507 * 10 ^ 70 +
        7227281342333822355144321870614595368788080228378532836384760019406080) * 10 ^ 70 +
        2593610506673405026324405827987194454530984445805871564408966889990941) * 10 ^ 70 +
        7039668221943618537638283943327540266674181142886154981006324010487788) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (457 - x)) = _
  rw [show 458 = 115 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 26 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (458 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (458 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_458 :
    recurrence4Scalar2First.coeff 458 =
      -((((962942096415956938 * 10 ^ 70 +
        8958706331299452639714972670212197414850212920352600302192655097084628) * 10 ^ 70 +
        2848740835636425123375892693835332915213833656889745098176764271266061) * 10 ^ 70 +
        8750150566035929992480309941977109921140220354707190981324548645042589) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (458 - x)) = _
  rw [show 459 = 116 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 25 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (459 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (459 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_459 :
    recurrence4Scalar2First.coeff 459 =
      ((((122612234534018458 * 10 ^ 70 +
        2719032733322363919627715544278106511487400621091850375900593614659471) * 10 ^ 70 +
        7575058071684383144530750324440816290377612147671870521263137270089019) * 10 ^ 70 +
        1165469295276547765588789529507939620359885817420931757293373381566692) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (459 - x)) = _
  rw [show 460 = 117 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 24 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (460 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (460 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_460 :
    recurrence4Scalar2First.coeff 460 =
      -((((11684492717202812 * 10 ^ 70 +
        4131219421089023842050474820071094395804257947819241511473446606558343) * 10 ^ 70 +
        2752894960079289658738632036879087234261697425028455626314615600127143) * 10 ^ 70 +
        1678800580022345669686886195229128349049799719256615697478171869124468) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (460 - x)) = _
  rw [show 461 = 118 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 23 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (461 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (461 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_461 :
    recurrence4Scalar2First.coeff 461 =
      ((((810652243521863 * 10 ^ 70 +
        7611763623739317668976794096193734866880318407475567133924175941146542) * 10 ^ 70 +
        3307056930416969673775888252132071057969523193206735415454634607113164) * 10 ^ 70 +
        2566184432947125934175618754774580352004097414457196246163908693215115) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (461 - x)) = _
  rw [show 462 = 119 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 22 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (462 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (462 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_462 :
    recurrence4Scalar2First.coeff 462 =
      -((((31098057497650 * 10 ^ 70 +
        1550918780208856693099969402537202404033704679726332243955578232845561) * 10 ^ 70 +
        1976218839341159846929874102888382157700600612753176329208668061873154) * 10 ^ 70 +
        8373806655966140678030597546456535884531910343587620676530120282045372) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (462 - x)) = _
  rw [show 463 = 120 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 21 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (463 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (463 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_463 :
    recurrence4Scalar2First.coeff 463 =
      -((((1232417610280 * 10 ^ 70 +
        8575467738094348721523590959320749165549827291254803963833062243148423) * 10 ^ 70 +
        4305657325861037953305512291315834411470217813458407784099937135063345) * 10 ^ 70 +
        3276593444831093194985534301746649634398310030595351990860498500730976) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (463 - x)) = _
  rw [show 464 = 121 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 20 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (464 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (464 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_464 :
    recurrence4Scalar2First.coeff 464 =
      ((((350671260261 * 10 ^ 70 +
        7074874029648885816655426013335327080673111871986556855095974882997847) * 10 ^ 70 +
        1097219286815978689766145425789615739161632024012917825097324532021147) * 10 ^ 70 +
        9725676826757690352784367647182526900402892148053818329296260442311746) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (464 - x)) = _
  rw [show 465 = 122 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 19 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (465 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (465 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_465 :
    recurrence4Scalar2First.coeff 465 =
      -((((35873672619 * 10 ^ 70 +
        0514183142993353053457951735482594115579041194244929749429019905650586) * 10 ^ 70 +
        7133110743711291817542533392965672341185345010507913298489904936342607) * 10 ^ 70 +
        3214261518355482992748138337077459727330122448391570818281924509342233) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (465 - x)) = _
  rw [show 466 = 123 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 18 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (466 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (466 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_466 :
    recurrence4Scalar2First.coeff 466 =
      ((((2379543398 * 10 ^ 70 +
        9123957138387920675736138262995471557065725110048512971571554581211397) * 10 ^ 70 +
        3363242206998291104522815729419578724564507013699069603407387458247132) * 10 ^ 70 +
        2849549676596835114711232734173707641082234465079402388281138636431609) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (466 - x)) = _
  rw [show 467 = 124 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 17 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (467 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (467 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_467 :
    recurrence4Scalar2First.coeff 467 =
      -((((101084610 * 10 ^ 70 +
        2258755300430833521954839657134269589044222853767103096088619186337887) * 10 ^ 70 +
        9793635048849158955660338870699458911949161091002680541423233553672399) * 10 ^ 70 +
        6148161230273283036019042688724032811341179406540302516900055629792520) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (467 - x)) = _
  rw [show 468 = 125 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 16 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_467_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (468 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (468 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_468 :
    recurrence4Scalar2First.coeff 468 =
      ((((1478320 * 10 ^ 70 +
        1180263524344488874044081048075029540842429162194532546640547477565544) * 10 ^ 70 +
        3719031529100411012460498764099600736786867552565553869001511372381757) * 10 ^ 70 +
        7701545659603579121565295974934210190279586450003558625722882104513539) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (468 - x)) = _
  rw [show 469 = 126 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 15 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_468_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (469 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (469 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_469 :
    recurrence4Scalar2First.coeff 469 =
      ((((147605 * 10 ^ 70 +
        3771208226105149860531171876941361956273487826967362314205882441558000) * 10 ^ 70 +
        9050768747613030461070236743546078438707758897442678917774073777801792) * 10 ^ 70 +
        3329608371456531437474179591812027538053254473399537268875498826276207) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (469 - x)) = _
  rw [show 470 = 127 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 14 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_469_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (470 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (470 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_470 :
    recurrence4Scalar2First.coeff 470 =
      -((((13293 * 10 ^ 70 +
        2857178124705420180380546140523565916271212136566630317847115941299699) * 10 ^ 70 +
        1708927216763390948682784378650934656960163786413152795767599377853822) * 10 ^ 70 +
        2982686098447230430983436075458749455922231311729567802038525626435871) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (470 - x)) = _
  rw [show 471 = 128 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 13 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_470_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (471 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (471 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_471 :
    recurrence4Scalar2First.coeff 471 =
      ((((529 * 10 ^ 70 +
        3729335325829315707287343703267962558082001836408462415827771509862883) * 10 ^ 70 +
        4172402177271237458291195927984248877952047907535906036996018753622072) * 10 ^ 70 +
        3338648564620399770553647705910924851372384068064950553544774563715361) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (471 - x)) = _
  rw [show 472 = 129 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 12 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_471_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (472 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (472 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_472 :
    recurrence4Scalar2First.coeff 472 =
      -((((7 * 10 ^ 70 +
        9475657016837826362329622939872558752961354517569283148107597857462864) * 10 ^ 70 +
        8616069641317627000782870650200832998620685651192630574882353717788840) * 10 ^ 70 +
        9807694594879848748893483215206877898094363994221531043585243559853270) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (472 - x)) = _
  rw [show 473 = 130 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 11 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_472_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (473 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (473 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_473 :
    recurrence4Scalar2First.coeff 473 =
      -(((2550161981577424067309540459870061418583857316283186311758988192800271 * 10 ^ 70 +
        0334551651814367207108262636007826901468155173244576121441187649679535) * 10 ^ 70 +
        2063681026199669386111459672755873165666011276338098286529650376895616) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (473 - x)) = _
  rw [show 474 = 131 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 10 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_473_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (474 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (474 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_474 :
    recurrence4Scalar2First.coeff 474 =
      (((152402132835918636099533795149434900348413042357838653569376637457927 * 10 ^ 70 +
        8390719925536170870576451628165672638936022523033510252504770056077952) * 10 ^ 70 +
        7171947927251617692493267336898318576808076757860483717272868498335133) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (474 - x)) = _
  rw [show 475 = 132 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 9 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_474_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (475 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (475 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_475 :
    recurrence4Scalar2First.coeff 475 =
      -(((2174519261213629884079425324732223812494938280672277283517925465479 * 10 ^ 70 +
        1539429961126495022991399933643179678013542688333224062931791104364822) * 10 ^ 70 +
        6849056803802013440102401994333049720296720515104639874691692917262522) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (475 - x)) = _
  rw [show 476 = 133 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 8 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_475_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (476 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (476 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_476 :
    recurrence4Scalar2First.coeff 476 =
      -(((36174965947821075771195146326023511170433436076431347728375510260 * 10 ^ 70 +
        0222786599261921443021136921208886682281757197335492888071229272624255) * 10 ^ 70 +
        6129591048245520051995140430611993518536867700495351023106610451033507) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (476 - x)) = _
  rw [show 477 = 134 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 7 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_476_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (477 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (477 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_477 :
    recurrence4Scalar2First.coeff 477 =
      (((1226048030242330048423300804033595396764063486143832296684503951 * 10 ^ 70 +
        5174427207258342747200989959077204957148806817580827914503044919137617) * 10 ^ 70 +
        1433313420943193120993100014553049457440438368952485148871165049021778) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (477 - x)) = _
  rw [show 478 = 135 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 6 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_477_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (478 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (478 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_478 :
    recurrence4Scalar2First.coeff 478 =
      (((1892267891894143911451085671725144793351363644422925735906944 * 10 ^ 70 +
        1450326049842363113349619973812294524226910537555242148502626920124621) * 10 ^ 70 +
        2821717081768612224362466615639259230231570423943587895767082084815392) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (478 - x)) = _
  rw [show 479 = 136 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 5 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (479 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (479 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_479 :
    recurrence4Scalar2First.coeff 479 =
      -(((237609612596318344611592443147032117772384612052349525898494 * 10 ^ 70 +
        4092370387523049094365212884890622438581321802224052581942949259164264) * 10 ^ 70 +
        6932304349969277994476316367007101773957917239976498844948438892927982) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (479 - x)) = _
  rw [show 480 = 137 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 4 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (480 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (480 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_480 :
    recurrence4Scalar2First.coeff 480 =
      -(((238048090170155631896385137316553283717988378658311390704 * 10 ^ 70 +
        7495929736104247142634836013429201458764141171896925266318375144550409) * 10 ^ 70 +
        5027148427570634942393031927653959648246505743084835857160238499823521) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (480 - x)) = _
  rw [show 481 = 138 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 3 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (481 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (481 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_481 :
    recurrence4Scalar2First.coeff 481 =
      (((22517157687956821345184160197478957126214544582508571508 * 10 ^ 70 +
        2941413690421669379400100445784754368085713623645784957024973417802798) * 10 ^ 70 +
        5118409515113039997815030177067647704241816802020058481732672530569180) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (481 - x)) = _
  rw [show 482 = 139 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 2 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (482 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (482 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_482 :
    recurrence4Scalar2First.coeff 482 =
      (((65221353532332533608294419979125114843529336430959321 * 10 ^ 70 +
        5295086062089925556978913603334035962681128437840861238098687208334692) * 10 ^ 70 +
        4122306511970863136420563649384680168403317447162641263032489529459612) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (482 - x)) = _
  rw [show 483 = 140 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 1 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (483 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (483 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_483 :
    recurrence4Scalar2First.coeff 483 =
      -(((885719521657088566079914194109705382936587617624816 * 10 ^ 70 +
        0553609614918198746854917293737669920739552444217769336877257121342347) * 10 ^ 70 +
        4662760976289649671450411754849124609288561494534538986447559302442206) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (483 - x)) = _
  rw [show 484 = 141 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (484 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (484 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_484 :
    recurrence4Scalar2First.coeff 484 =
      -(((3759142129374992246191375887541726834374091759797 * 10 ^ 70 +
        7664269033777766510687405967881373574167260103971622385149728013929694) * 10 ^ 70 +
        4966961569779964640485330602233784067770791350445570812620863815267084) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (484 - x)) = _
  rw [show 485 = 142 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 31 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (485 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (485 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_485 :
    recurrence4Scalar2First.coeff 485 =
      (((15584936224997584109743646954319736224420474905 * 10 ^ 70 +
        2163362174922454620887124864248595111842910834344479981402865884273388) * 10 ^ 70 +
        2604261504929404603774323871541509311099022064610742313092225793626636) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (485 - x)) = _
  rw [show 486 = 143 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 30 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (486 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 314,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (486 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_486 :
    recurrence4Scalar2First.coeff 486 =
      (((86630564685915262035269420345292525917741834 * 10 ^ 70 +
        2196437399053434932950560028479680415758670477417250468859701134441797) * 10 ^ 70 +
        4334029285642396704193277130426887811645757562547442120850367630745710) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (486 - x)) = _
  rw [show 487 = 144 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 29 +
      314 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (487 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 315,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (487 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_487 :
    recurrence4Scalar2First.coeff 487 =
      -(((130138071764650013101096281068775272656118 * 10 ^ 70 +
        4278436600247451937975541082886365461204690896712095738052550483576316) * 10 ^ 70 +
        5855696011172592959818001843714822064746836130354597633153085753272588) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (487 - x)) = _
  rw [show 488 = 145 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 28 +
      315 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (488 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 316,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (488 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_488 :
    recurrence4Scalar2First.coeff 488 =
      -(((964264856873487733061436047660878722430 * 10 ^ 70 +
        1670645998912844482668011243373863421370821133860284339780240342018907) * 10 ^ 70 +
        7568128276050296535645660618834469958385748784368299222899925101349970) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (488 - x)) = _
  rw [show 489 = 146 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 27 +
      316 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (489 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 317,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (489 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_489 :
    recurrence4Scalar2First.coeff 489 =
      (((681518019404502408120340868413574927 * 10 ^ 70 +
        3008151318166527491167823248866293876655926151499158556026933149005526) * 10 ^ 70 +
        7629749891221408990223009263266975426532498266493103072003347288959200) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (489 - x)) = _
  rw [show 490 = 147 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 26 +
      317 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (490 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 318,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (490 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_490 :
    recurrence4Scalar2First.coeff 490 =
      (((5912400997949995007095020946034077 * 10 ^ 70 +
        3795535724657251439950326845337941405502416611236849482088573608086650) * 10 ^ 70 +
        9106633351085622506620516361950232096296625802593636047508777945814939) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (490 - x)) = _
  rw [show 491 = 148 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 25 +
      318 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (491 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 319,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (491 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_491 :
    recurrence4Scalar2First.coeff 491 =
      -(((3397953288910819341252694809932 * 10 ^ 70 +
        9033513416564964432764666642175364262099554945306152483708285446121531) * 10 ^ 70 +
        0608464308386087970029031843585536249328381239697215526547554605757410) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (491 - x)) = _
  rw [show 492 = 149 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 24 +
      319 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (492 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 320,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (492 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_492 :
    recurrence4Scalar2First.coeff 492 =
      -(((19960418731174918942675863143 * 10 ^ 70 +
        8514587439069320323035262371145093885508217952234419216559348284034889) * 10 ^ 70 +
        1802720099387596485581666514220076116771489618845413497626615317113052) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (492 - x)) = _
  rw [show 493 = 150 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 23 +
      320 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (493 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 321,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (493 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_493 :
    recurrence4Scalar2First.coeff 493 =
      (((14672512621614762089286200 * 10 ^ 70 +
        0439249627168447793446652617102173434825843583327310728943171819686239) * 10 ^ 70 +
        8559682277665935222223078174423398646526690297663731088553764283377585) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (493 - x)) = _
  rw [show 494 = 151 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 22 +
      321 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (494 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 322,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (494 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_494 :
    recurrence4Scalar2First.coeff 494 =
      (((30751600371785934062365 * 10 ^ 70 +
        9729215761199047340757157411126716573130345750684652898278520376166696) * 10 ^ 70 +
        9308903894352501613231399974488105822950162163337914218274970670717382) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (494 - x)) = _
  rw [show 495 = 152 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 21 +
      322 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (495 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 323,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (495 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_495 :
    recurrence4Scalar2First.coeff 495 =
      -(((30493122735631778756 * 10 ^ 70 +
        3571311600392521999360450329983412392681507214118560708874662961265265) * 10 ^ 70 +
        4761646109189609124600154454190383051914931611390469991627685411115803) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (495 - x)) = _
  rw [show 496 = 153 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 20 +
      323 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (496 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 324,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (496 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_496 :
    recurrence4Scalar2First.coeff 496 =
      -(((10473124263342328 * 10 ^ 70 +
        1826377632418646901561687198208208753773803511924074577171845171027283) * 10 ^ 70 +
        6481797679366199807422928943466562825738724584597494578481212182471112) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (496 - x)) = _
  rw [show 497 = 154 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 19 +
      324 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (497 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 325,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (497 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_497 :
    recurrence4Scalar2First.coeff 497 =
      (((15909977056943 * 10 ^ 70 +
        3879473511673068937596166476535706362007460691874206150118865234756407) * 10 ^ 70 +
        4601100720519610269901021455579383612064399583750745381248617585423860) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (497 - x)) = _
  rw [show 498 = 155 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 18 +
      325 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (498 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 326,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (498 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_498 :
    recurrence4Scalar2First.coeff 498 =
      -(((2049220354 * 10 ^ 70 +
        8494599600372486062035924106198765833812593392869934314993311907007488) * 10 ^ 70 +
        0842193227975459951287262971826960377543624182245352521929608218970681) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (498 - x)) = _
  rw [show 499 = 156 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 17 +
      326 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (499 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 327,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (499 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_499 :
    recurrence4Scalar2First.coeff 499 =
      -(((1268857 * 10 ^ 70 +
        6162623721071894083129655464050261213924086411172069457073709376282751) * 10 ^ 70 +
        1442634761733404539718938804681217770990225761370985027353487368797921) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (499 - x)) = _
  rw [show 500 = 157 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 16 +
      327 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (500 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 328,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (500 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_500 :
    recurrence4Scalar2First.coeff 500 =
      (((260 * 10 ^ 70 +
        4812782993051325547754023819130839863284303250559075781805099546875124) * 10 ^ 70 +
        0769070484437742765478673919550657051167125969659311535844292965130716) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (500 - x)) = _
  rw [show 501 = 158 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 15 +
      328 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (501 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 329,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (501 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_501 :
    recurrence4Scalar2First.coeff 501 =
      ((18134678894815770625391714068569329973752587747028388811030182028319 * 10 ^ 70 +
        8641076104039858097050332316987829594398587891055646518375987639405871) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (501 - x)) = _
  rw [show 502 = 159 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 14 +
      329 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (502 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 330,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (502 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_502 :
    recurrence4Scalar2First.coeff 502 =
      -((24069170744876608073069079600178773270889641204203899890454585565 * 10 ^ 70 +
        2782187034597289463775359174344619867478976920032353968612756685680049) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (502 - x)) = _
  rw [show 503 = 160 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 13 +
      330 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (503 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 331,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (503 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_503 :
    recurrence4Scalar2First.coeff 503 =
      ((801757337469419034443160056795467026476551359296597498531548 * 10 ^ 70 +
        0362551547351592271978323954442450454547248967751497167795411745036974) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (503 - x)) = _
  rw [show 504 = 161 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 12 +
      331 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (504 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 332,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (504 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_504 :
    recurrence4Scalar2First.coeff 504 =
      ((10261870758091368067280995228041343105017459960008092726 * 10 ^ 70 +
        9020321086759925373809763916300461964002226761516209226311188677515830) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (504 - x)) = _
  rw [show 505 = 162 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 11 +
      332 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (505 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 333,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (505 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_505 :
    recurrence4Scalar2First.coeff 505 =
      -((516751208568411712055358820449425805702438736646520 * 10 ^ 70 +
        0157546564943803517023190280222507124091777207402042266441455385405630) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (505 - x)) = _
  rw [show 506 = 163 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 10 +
      333 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (506 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 334,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (506 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_506 :
    recurrence4Scalar2First.coeff 506 =
      ((2294697852220567538503827873345476459543750876 * 10 ^ 70 +
        6815261773827608621034003207252099118625661140840543439931303225392724) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (506 - x)) = _
  rw [show 507 = 164 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 9 +
      334 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (507 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 335,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (507 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_507 :
    recurrence4Scalar2First.coeff 507 =
      ((10018448708761985975159506752335093646339 * 10 ^ 70 +
        5519694785923614122547604991845215803943073128368829130900402811569999) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (507 - x)) = _
  rw [show 508 = 165 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 8 +
      335 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_507_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (508 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 336,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (508 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_508 :
    recurrence4Scalar2First.coeff 508 =
      -((52273326467983589116817890805050017 * 10 ^ 70 +
        8617729180679691502668723482476272735171242783467028727359619370496392) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (508 - x)) = _
  rw [show 509 = 166 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 7 +
      336 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_508_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (509 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 337,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (509 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_509 :
    recurrence4Scalar2First.coeff 509 =
      ((21265049294964088909999470325 * 10 ^ 70 +
        2779001011881598336352017998896374926536359650381047200043143825243096) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (509 - x)) = _
  rw [show 510 = 167 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 6 +
      337 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_509_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (510 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 338,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (510 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_510 :
    recurrence4Scalar2First.coeff 510 =
      ((13319885010094676545618 * 10 ^ 70 +
        6346572874957911382553060068890166936832305299672023712058098575695002) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (510 - x)) = _
  rw [show 511 = 168 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 5 +
      338 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_510_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (511 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 339,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (511 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_511 :
    recurrence4Scalar2First.coeff 511 =
      -((5358798596695867 * 10 ^ 70 +
        0902477614109894189963715864681961650380136894287248196640266926044057) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (511 - x)) = _
  rw [show 512 = 169 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 4 +
      339 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_511_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_512_prefix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (512 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (512 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_512_suffix_zero :
    (∑ x ∈ Finset.range 340,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (512 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_512 :
    recurrence4Scalar2First.coeff 512 =
      ((113699392 * 10 ^ 70 +
        7841090890155353766512537773657870373357887511187222216876472438769690) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 513,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (512 - x)) = _
  rw [show 513 = 170 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 3 +
      340 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_512_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_512_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_513_prefix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (513 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (513 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_513_suffix_zero :
    (∑ x ∈ Finset.range 341,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (513 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_513 :
    recurrence4Scalar2First.coeff 513 =
      ((1 * 10 ^ 70 +
        4579637339139980743858377678462896315282612147353071394610493174012911) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 514,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (513 - x)) = _
  rw [show 514 = 171 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 2 +
      341 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_513_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_513_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_514_prefix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (514 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (514 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_514_suffix_zero :
    (∑ x ∈ Finset.range 342,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (514 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_514 :
    recurrence4Scalar2First.coeff 514 =
      (-208462106852790140363836899991423728946573507966299777847604670 : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 515,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (514 - x)) = _
  rw [show 515 = 172 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 1 +
      342 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_514_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_514_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
