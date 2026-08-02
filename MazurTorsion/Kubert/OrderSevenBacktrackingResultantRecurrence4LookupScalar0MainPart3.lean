/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar0Main_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (383 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (383 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_383 :
    recurrence4Scalar0Main.coeff 383 =
      -((((1550281776055281683787193889001610444182344719675849098661502316239 * 10 ^ 70 +
        8965633575460153653180983948933927725096511314800372923359167589747795) * 10 ^ 70 +
        8595039959943704505210564080382486990998263857309452055397603726022804) * 10 ^ 70 +
        8816821870729057489575162989332600802330196570966785379009558369867011) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (383 - x)) = _
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
    rw [show 219 = 12 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (384 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (384 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_384 :
    recurrence4Scalar0Main.coeff 384 =
      ((((89751622854329376054539901515347574672795440519505281114112251079 * 10 ^ 70 +
        8920603145033274815945308888908424438686551328542094901444790709067774) * 10 ^ 70 +
        4114075792076485555727522252814285470514861996429449213990700278440729) * 10 ^ 70 +
        3450671797389881656046967842971865622939348633594158414851577775056338) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (384 - x)) = _
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
    rw [show 219 = 11 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (385 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (385 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_385 :
    recurrence4Scalar0Main.coeff 385 =
      ((((109434099580917174100793396234022531074377449559865793944294208449 * 10 ^ 70 +
        7857937321622775915298338064248298399644744297437071481741221970234100) * 10 ^ 70 +
        9218988843047118580865865362127350858463540815073554284734019970294321) * 10 ^ 70 +
        4365313397436336460500017539677690528540643930280529694856779280055813) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (385 - x)) = _
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
    rw [show 219 = 10 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (386 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (386 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_386 :
    recurrence4Scalar0Main.coeff 386 =
      -((((78825841056154704991534175841469861816947792506350713157547358805 * 10 ^ 70 +
        5069552067950796446271422154513780288602922035168219745965481318078459) * 10 ^ 70 +
        9091289922504510036703477387340163755166844853315657194291583944928547) * 10 ^ 70 +
        6277335757349481927832272986823680522846604768164182307130868975879988) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (386 - x)) = _
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
    rw [show 219 = 9 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (387 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (387 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_387 :
    recurrence4Scalar0Main.coeff 387 =
      ((((38258934127880910935897024597994966387088967546671767557802683595 * 10 ^ 70 +
        1864847996255874575281258485892889301518261720924076678336613698314103) * 10 ^ 70 +
        9309861310653682151950419885809219094539405571479613264746458771797052) * 10 ^ 70 +
        2151639691510720504299516367968456578331602551102496919166024666312821) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (387 - x)) = _
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
    rw [show 219 = 8 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (388 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (388 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_388 :
    recurrence4Scalar0Main.coeff 388 =
      -((((15923791005933361947914695473198992299285668877464185805107019486 * 10 ^ 70 +
        7256754959324629351366361523893559463070482132041759638386581362381725) * 10 ^ 70 +
        0215871677737875875453012989276724790401799240704377658867152431306918) * 10 ^ 70 +
        7082202730235318499601062858911894609217318160598082981466409564071544) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (388 - x)) = _
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
    rw [show 219 = 7 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (389 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (389 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_389 :
    recurrence4Scalar0Main.coeff 389 =
      ((((6111019277396755183412941355772947816824591056464974468053344533 * 10 ^ 70 +
        5553965027196376469045097340850906528710010503465422952811679437071454) * 10 ^ 70 +
        6174078643504288723299232878137525498660744945949039880733954228146109) * 10 ^ 70 +
        3520394735572730793682155624821575007166617458146533054521100487470623) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (389 - x)) = _
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
    rw [show 219 = 6 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (390 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (390 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_390 :
    recurrence4Scalar0Main.coeff 390 =
      -((((2247135996383902147597092922856576711279585666759434004707899533 * 10 ^ 70 +
        6199721684893881038287836910616363392540168206739487280641357716605798) * 10 ^ 70 +
        9773893248026819999662536062198553787801472641223656830637916800674869) * 10 ^ 70 +
        7313015348923021131285526579458142617406767887565237230722526727884946) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (390 - x)) = _
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
    rw [show 219 = 5 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (391 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (391 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_391 :
    recurrence4Scalar0Main.coeff 391 =
      ((((814657803954929209114942857554277772980913352643379954341285694 * 10 ^ 70 +
        0848827963735396870269923111611757914927573997850066077847807708207447) * 10 ^ 70 +
        7652950508797977708034405718819852296690894167353850244478356337005284) * 10 ^ 70 +
        1338930958726714984407659626246190227347201179794849917718677010002112) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (391 - x)) = _
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
    rhs
    rw [show 219 = 4 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (392 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (392 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_392 :
    recurrence4Scalar0Main.coeff 392 =
      -((((298057461460808952664973447601826126856914279534513876913918146 * 10 ^ 70 +
        9365161284723152119678033946318867363595851802917710393136355563784608) * 10 ^ 70 +
        6793373172904857096741814707592827272106838245293212057212425738875106) * 10 ^ 70 +
        7564045508050842433187664023621612757669387238872173199153647253883775) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (392 - x)) = _
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
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 3 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (393 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (393 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_393 :
    recurrence4Scalar0Main.coeff 393 =
      ((((111817284825224806392120164813829396512789383724853781446771918 * 10 ^ 70 +
        7373940831139556075025344708582234383505478132891363321682653928296513) * 10 ^ 70 +
        4408622811350811621042747020499146214946479410686815744334471343652518) * 10 ^ 70 +
        5792423954206240139299857781623498936157414528055835362368509315721092) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (393 - x)) = _
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
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 2 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (394 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (394 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_394 :
    recurrence4Scalar0Main.coeff 394 =
      -((((43212113604562776326119719215534456018098523940816197496608601 * 10 ^ 70 +
        4684066653506294522732091970063398227083850180552705418747994677504712) * 10 ^ 70 +
        5417613950887411825603704909876111935709370372047811611639504704704363) * 10 ^ 70 +
        0281495304309754083478992798604006643377484035836058671616560684010298) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (394 - x)) = _
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
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 1 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (395 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (395 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_395 :
    recurrence4Scalar0Main.coeff 395 =
      ((((17085655710863461887359743457224333914448634373906432519756481 * 10 ^ 70 +
        8293602479011342400850693264565914988182058158126862559309078047728513) * 10 ^ 70 +
        0705202143556448663366234499065869668401389745951443116699429006404004) * 10 ^ 70 +
        5356039743795250667383810266863860728964146292412190228716953519240734) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (395 - x)) = _
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
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (396 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (396 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_396 :
    recurrence4Scalar0Main.coeff 396 =
      -((((6818445211343368579938946838094353354459267983801489313976931 * 10 ^ 70 +
        2875292686813310918060647437820521769551516162247610639803093797650739) * 10 ^ 70 +
        0421291963785606765160760024891059076711781801750716424069568492842543) * 10 ^ 70 +
        2681312208895795600528680803210884839929412956430211370806737261337279) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (396 - x)) = _
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
    rw [show 251 = 31 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (397 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (397 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_397 :
    recurrence4Scalar0Main.coeff 397 =
      ((((2706680240162263082690605420404427712875358527719281273126147 * 10 ^ 70 +
        6351295992112878784245274474947883604978415597730218124112832641902799) * 10 ^ 70 +
        7420288000758245480468899623702330285123681759706687832729425254380241) * 10 ^ 70 +
        0484535271235069721097346171772671920592305148971461351322184025676154) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (397 - x)) = _
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
    rw [show 251 = 30 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (398 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (398 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_398 :
    recurrence4Scalar0Main.coeff 398 =
      -((((1055979036560296983134087104754577266619855657515407610625114 * 10 ^ 70 +
        4216133857885359260199097840112066196293171155868659929438211173092736) * 10 ^ 70 +
        0478096365798596782565960671364737132343414173391418299545721325707315) * 10 ^ 70 +
        2698213876701351667970270318209092775190947813500800668171252661851523) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (398 - x)) = _
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
    rw [show 251 = 29 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (399 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (399 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_399 :
    recurrence4Scalar0Main.coeff 399 =
      ((((401398494743892307907291052348544221238885254278649543385853 * 10 ^ 70 +
        5961518464946550344758268360956962403126084253494502072930071271642182) * 10 ^ 70 +
        9562057825325269635016625711329439246970722948566019262978150069940464) * 10 ^ 70 +
        2790199870579970666031669651049139162145837253189962752846807394048427) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (399 - x)) = _
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
    rw [show 251 = 28 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (400 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (400 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_400 :
    recurrence4Scalar0Main.coeff 400 =
      -((((147787998676287650800763584603589393573272894506495210444223 * 10 ^ 70 +
        8742701014779676248989807078689563834300182973215865738570473542727002) * 10 ^ 70 +
        3278092577435192947440235574427956956805559143407328563959847237993220) * 10 ^ 70 +
        8506659663049824273408714656429903946337751305236207446611987368552818) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (400 - x)) = _
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
    rw [show 251 = 27 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (401 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (401 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_401 :
    recurrence4Scalar0Main.coeff 401 =
      ((((52488000670668751257711949397197092009799618029236247917248 * 10 ^ 70 +
        9865217717071965908736377786078385397166654431617927781688604694574330) * 10 ^ 70 +
        8183498493972102853133628597986676236928007975971843366224933732886576) * 10 ^ 70 +
        3510276743060868999683785995147347487508562576233841308699156041049510) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (401 - x)) = _
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
    rw [show 251 = 26 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (402 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (402 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_402 :
    recurrence4Scalar0Main.coeff 402 =
      -((((17923459111933868003168799254010705051307530849553116143178 * 10 ^ 70 +
        2437564918401379849783838325023384334325377666678701834653187165239232) * 10 ^ 70 +
        0901420069144361761371227864899058826323230342478641608643190308889673) * 10 ^ 70 +
        6395061744734664511714240156466230023822562432781768222494223622369244) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (402 - x)) = _
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
    rw [show 251 = 25 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (403 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (403 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_403 :
    recurrence4Scalar0Main.coeff 403 =
      ((((5865810805140931420543026146487926924688235746587768720908 * 10 ^ 70 +
        4158580455418504093542303404157479729590731649077534154454409785521809) * 10 ^ 70 +
        7082399513366273958131838259904923710023438450229312149865146815285722) * 10 ^ 70 +
        7172072670287012841270964695197756980329853914185353076693839475874078) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (403 - x)) = _
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
    rw [show 251 = 24 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (404 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (404 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_404 :
    recurrence4Scalar0Main.coeff 404 =
      -((((1832547868667909447803691192024041707349770927750628455586 * 10 ^ 70 +
        7542380954204453522878166873675126772873546363396094872511668681473729) * 10 ^ 70 +
        8780658012426345234040527696413149144612124419661319330054052406363001) * 10 ^ 70 +
        0001667242135344240488968554072637443060383549642759020165742050797331) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (404 - x)) = _
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
    rw [show 251 = 23 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (405 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (405 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_405 :
    recurrence4Scalar0Main.coeff 405 =
      ((((543370606842792471433799940897282001087875418120738089376 * 10 ^ 70 +
        9631985063383176652492430775442041356208321282555949454733153709739260) * 10 ^ 70 +
        5419294087869958506854140493057537836935752958582784673152231798882896) * 10 ^ 70 +
        7964521675676160158642007749155897329785060194768430492336946979726497) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (405 - x)) = _
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
    rw [show 251 = 22 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (406 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (406 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_406 :
    recurrence4Scalar0Main.coeff 406 =
      -((((151480281992675671525902224977866015436825090402900860294 * 10 ^ 70 +
        8795274762958023499035713117339821224488555128748840812103478297929766) * 10 ^ 70 +
        8337971118611195861371760486364807651465179333927582882726610781034600) * 10 ^ 70 +
        8292107217544269997595621867523035621721105320835149969437599202250911) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (406 - x)) = _
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
    rw [show 251 = 21 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (456 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (456 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_456 :
    recurrence4Scalar0Main.coeff 456 =
      -((((170231733573006247089029800 * 10 ^ 70 +
        3696051216029656810014358597161066763460293089619645279986648288980246) * 10 ^ 70 +
        7946138177248065982852556830357488088406145222300183830125663327198612) * 10 ^ 70 +
        4699778996573228113516428393272066511956795935823587602111971179183140) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (456 - x)) = _
  rw [show 457 = 110 +
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
  rw [recurrence4Scalar0Main_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (457 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (457 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_457 :
    recurrence4Scalar0Main.coeff 457 =
      -((((806043343693466965665193 * 10 ^ 70 +
        6492278904669174897688294666440296609701138419323146090194310561912045) * 10 ^ 70 +
        6612460421304115546069018394267615199642195508373630832180430280659712) * 10 ^ 70 +
        9543704895034832665409455866535795766187263358942774384649801790261655) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (457 - x)) = _
  rw [show 458 = 111 +
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
  rw [recurrence4Scalar0Main_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (458 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (458 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_458 :
    recurrence4Scalar0Main.coeff 458 =
      ((((2971370154782735670998825 * 10 ^ 70 +
        1911534641334231007332653604248460283188016364379232882805027305080565) * 10 ^ 70 +
        8027118230024138520085115162342854023404829768389477402036441974352590) * 10 ^ 70 +
        7310018152995722278149512180504772185440936865736085633053584535298950) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (458 - x)) = _
  rw [show 459 = 112 +
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
  rw [recurrence4Scalar0Main_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (459 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (459 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_459 :
    recurrence4Scalar0Main.coeff 459 =
      -((((684744383798048010432897 * 10 ^ 70 +
        3335568731615560137904410477337550030991472318321149391713356392599126) * 10 ^ 70 +
        9444570453512920762627404634394821524585008487630533177897763094266631) * 10 ^ 70 +
        1258615551173633612601032064329570480260968524141584823800759224399911) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (459 - x)) = _
  rw [show 460 = 113 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (460 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (460 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_460 :
    recurrence4Scalar0Main.coeff 460 =
      ((((112374557587881713329699 * 10 ^ 70 +
        7167465066042683403253818193239042738477654399364862331152408287987237) * 10 ^ 70 +
        3425606858418167646878059057783170176176407858078900780844226675974688) * 10 ^ 70 +
        0925173751708707446260979901407874662508630649369935894808927495382272) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (460 - x)) = _
  rw [show 461 = 114 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 31 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (461 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (461 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_461 :
    recurrence4Scalar0Main.coeff 461 =
      -((((15315278010106342086861 * 10 ^ 70 +
        3979795806247003658740536378885329265843974899918775432640566071037251) * 10 ^ 70 +
        8593397029531917240611114085211708747233550537130394808152275199441559) * 10 ^ 70 +
        5970676538866071459052764821750068666303110015973633139025364584773978) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (461 - x)) = _
  rw [show 462 = 115 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 30 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (462 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (462 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_462 :
    recurrence4Scalar0Main.coeff 462 =
      ((((1803555289147661013658 * 10 ^ 70 +
        0040383441561599164596403598297346031592278409168784632215936134838609) * 10 ^ 70 +
        7896466829421102705732128980008069330197356164913302237624618022882294) * 10 ^ 70 +
        0018543350952833105229137911886116805011388265313669559871062422726743) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (462 - x)) = _
  rw [show 463 = 116 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 29 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (463 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (463 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_463 :
    recurrence4Scalar0Main.coeff 463 =
      -((((184267806378409273237 * 10 ^ 70 +
        4146048942801928957054398722635427683364025254317745169299889175535923) * 10 ^ 70 +
        1323395440532558494644666531874998371474224654792125124898990991129642) * 10 ^ 70 +
        0798667710262277874540470591762563447729454088531704207199151279964604) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (463 - x)) = _
  rw [show 464 = 117 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 28 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (464 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (464 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_464 :
    recurrence4Scalar0Main.coeff 464 =
      ((((15981881971703218453 * 10 ^ 70 +
        9928528461095699744059485283411167929843889107094019588969220177951745) * 10 ^ 70 +
        9734765434217898808504511428083318178572167854942853177171978847732785) * 10 ^ 70 +
        2162859405055143744043892981875127938977500585399786849929496895822733) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (464 - x)) = _
  rw [show 465 = 118 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 27 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (465 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (465 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_465 :
    recurrence4Scalar0Main.coeff 465 =
      -((((1099331096759095143 * 10 ^ 70 +
        5810345137825601306460739264071024394839529367390742231672920637276567) * 10 ^ 70 +
        9324276096827542627258383637424300771222454514961657973263365675072497) * 10 ^ 70 +
        8301096960851404888628406702405247970724431912123723919299636556395022) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (465 - x)) = _
  rw [show 466 = 119 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 26 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (466 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (466 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_466 :
    recurrence4Scalar0Main.coeff 466 =
      ((((46292120440690189 * 10 ^ 70 +
        8613469626113734904127475813798053236618219987447631077489072109336884) * 10 ^ 70 +
        5734809595272735119239529793211628740926228199780770485753667230380244) * 10 ^ 70 +
        8131670906978234815730901550513961493960870383920095938561028795087928) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (466 - x)) = _
  rw [show 467 = 120 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 25 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (467 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (467 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_467 :
    recurrence4Scalar0Main.coeff 467 =
      ((((1388769626578250 * 10 ^ 70 +
        1011798355852013203754043382243926897224042401976187595492916596508696) * 10 ^ 70 +
        6586004071220032321159716870216431704028385046481292864648922880181595) * 10 ^ 70 +
        4547131690175513481167367106504317192371101821499170647264057707068010) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (467 - x)) = _
  rw [show 468 = 121 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 24 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (468 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (468 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_468 :
    recurrence4Scalar0Main.coeff 468 =
      -((((544577938373236 * 10 ^ 70 +
        4372516811767061420995805097881001047749969166266307516954400015237299) * 10 ^ 70 +
        2353812996057445813107662744629052084551568499455678760907811750044180) * 10 ^ 70 +
        9162059976556249267172008625146278058156345065749252315741866604869739) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (468 - x)) = _
  rw [show 469 = 122 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 23 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (469 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (469 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_469 :
    recurrence4Scalar0Main.coeff 469 =
      ((((67298481011466 * 10 ^ 70 +
        7061457207290755229250995917734690512760644802693587790861401987088321) * 10 ^ 70 +
        3006227418657722162013262621312714404886118300738363808992863675109962) * 10 ^ 70 +
        8084370107293208194427485149697459304693433125245869435447948140051673) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (469 - x)) = _
  rw [show 470 = 123 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 22 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (470 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (470 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_470 :
    recurrence4Scalar0Main.coeff 470 =
      -((((5561478756777 * 10 ^ 70 +
        3130438983502631423221146469515860868947327154917594950159699145778790) * 10 ^ 70 +
        9774336595630537325217530840309588924027564275053442327419150042075047) * 10 ^ 70 +
        5508918063305284852011114577961831450543192931543273171186574506574990) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (470 - x)) = _
  rw [show 471 = 124 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 21 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (471 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (471 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_471 :
    recurrence4Scalar0Main.coeff 471 =
      ((((313141107871 * 10 ^ 70 +
        6246826471090763492616104097035878610205813112246909881593421431144414) * 10 ^ 70 +
        7988381993626039395988932603514582323588844724078358989304771465210146) * 10 ^ 70 +
        0277497319102539861207697431895533251488367266895035395263006922345209) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (471 - x)) = _
  rw [show 472 = 125 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 20 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (472 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (472 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_472 :
    recurrence4Scalar0Main.coeff 472 =
      -((((8008228878 * 10 ^ 70 +
        5139237849449807776035532201256738566219940853274079763731464435612239) * 10 ^ 70 +
        9409926457313277013560814643682487142014085316113494247670944397851510) * 10 ^ 70 +
        7273090257934228953023387896728919246419078989534673833608572469080139) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (472 - x)) = _
  rw [show 473 = 126 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 19 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (473 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (473 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_473 :
    recurrence4Scalar0Main.coeff 473 =
      -((((581220740 * 10 ^ 70 +
        3729181883637076657918643807343836992841755681204792357677378640810987) * 10 ^ 70 +
        0706646926971155672583065696337229645744183779671317726233101831485461) * 10 ^ 70 +
        7854809125754047422964500471615590150183065637387410067301246536394379) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (473 - x)) = _
  rw [show 474 = 127 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 18 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (474 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (474 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_474 :
    recurrence4Scalar0Main.coeff 474 =
      ((((92687418 * 10 ^ 70 +
        3348625672996026649786103705755333169303091665243239489193929487587252) * 10 ^ 70 +
        9614298246680270037287502466156205669849376794621336302706549315337080) * 10 ^ 70 +
        3847719220142698642326327241980901202105089697544587259721818440396165) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (474 - x)) = _
  rw [show 475 = 128 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 17 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (475 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (475 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_475 :
    recurrence4Scalar0Main.coeff 475 =
      -((((6626450 * 10 ^ 70 +
        0288891045067980274437115447898376011824375501055900453853627036269983) * 10 ^ 70 +
        9180206745933309083169299537767952324208192142275285660562487456288795) * 10 ^ 70 +
        4222405274367133071392179746471440653182624577348093168667813648277220) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (475 - x)) = _
  rw [show 476 = 129 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 16 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (476 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (476 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_476 :
    recurrence4Scalar0Main.coeff 476 =
      ((((280745 * 10 ^ 70 +
        0903755418426663812809286231528537986796332149104574158417154484310828) * 10 ^ 70 +
        3098312289428297069590471733799901641680080368366256744133262879867023) * 10 ^ 70 +
        2582763297348300643143659054823005371163642555379960318595946643767768) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (476 - x)) = _
  rw [show 477 = 130 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 15 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (477 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (477 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_477 :
    recurrence4Scalar0Main.coeff 477 =
      -((((4386 * 10 ^ 70 +
        6986894439439350507717852600221242526119781266098507159541750982167870) * 10 ^ 70 +
        3285352545774884096137705827301740375897009777773026452573351842601126) * 10 ^ 70 +
        3695224277931200314523597568459313984525902224230637938786430067678477) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (477 - x)) = _
  rw [show 478 = 131 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 14 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (478 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (478 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_478 :
    recurrence4Scalar0Main.coeff 478 =
      -((((297 * 10 ^ 70 +
        4619282470231940777162015307655939963962290220553150595420185739561399) * 10 ^ 70 +
        4231705032065520407224187244848985921275047161409531277862945122735646) * 10 ^ 70 +
        0286874049729618784201683804171660816643178621795004714805920962706274) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (478 - x)) = _
  rw [show 479 = 132 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 13 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (479 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (479 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_479 :
    recurrence4Scalar0Main.coeff 479 =
      ((((24 * 10 ^ 70 +
        5459066014848571018537617497827237632103376745418035009099243465866203) * 10 ^ 70 +
        3259201250266495152695709966303048287576795161094500789652897624708950) * 10 ^ 70 +
        8250676378707330425596499131742244969409690721787078251083796994548990) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (479 - x)) = _
  rw [show 480 = 133 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 12 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_479_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (480 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (480 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_480 :
    recurrence4Scalar0Main.coeff 480 =
      -(((7854790626573982776313279137526109674116439361434720953438541493218984 * 10 ^ 70 +
        5133994675719522147601111820973507171059378273630771248390899141734327) * 10 ^ 70 +
        3013455851842096768681327448301242493381195961180801546716450501076621) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (480 - x)) = _
  rw [show 481 = 134 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 11 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_480_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (481 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (481 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_481 :
    recurrence4Scalar0Main.coeff 481 =
      (((50668416491761280224966116601522809941182874119282088317712351281129 * 10 ^ 70 +
        3138016614799549486539977075708001574780638618004654043149284774797529) * 10 ^ 70 +
        0400219732541572695688319737568884791535781187695663678754799492171153) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (481 - x)) = _
  rw [show 482 = 135 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 10 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_481_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (482 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (482 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_482 :
    recurrence4Scalar0Main.coeff 482 =
      (((4903951331915762569058023903611514921628156633158295547057328042609 * 10 ^ 70 +
        9613876126610327122903462774880797896047889645982126146739505018293457) * 10 ^ 70 +
        5723502283094917811734390534635313653991820431532688219576089014030768) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (482 - x)) = _
  rw [show 483 = 136 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 9 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_482_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (496 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 320,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (496 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_496 :
    recurrence4Scalar0Main.coeff 496 =
      -(((17146244227673374488414009645687124594 * 10 ^ 70 +
        0967820089134055707593969173952423286396695294277863423399542383877694) * 10 ^ 70 +
        0473905428676288800953001355745657091003423727958738074794038056931631) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (496 - x)) = _
  rw [show 497 = 150 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 27 +
      320 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_496_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (497 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 321,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (497 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_497 :
    recurrence4Scalar0Main.coeff 497 =
      (((65009228768281422754384458907163687 * 10 ^ 70 +
        0669129485188552035555889483009929539103033825932936341950127546209470) * 10 ^ 70 +
        8464259367332577531727134710711940563309168899479728921605033480903339) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (497 - x)) = _
  rw [show 498 = 151 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 26 +
      321 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_497_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (498 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 322,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (498 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_498 :
    recurrence4Scalar0Main.coeff 498 =
      (((103484023676122439629180017766495 * 10 ^ 70 +
        7549186968933579907458507107783490873855959991308398823681137757758600) * 10 ^ 70 +
        4797140998874574451951411550897687594416740203185065359959546683907337) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (498 - x)) = _
  rw [show 499 = 152 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 25 +
      322 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_498_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (499 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 323,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (499 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_499 :
    recurrence4Scalar0Main.coeff 499 =
      -(((300665835954612908638604892043 * 10 ^ 70 +
        7725744623728787259071355765460681349638787105737121173259085697985344) * 10 ^ 70 +
        5361640021453004853801819324130610485567965935616583925514581344030238) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (499 - x)) = _
  rw [show 500 = 153 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 24 +
      323 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_499_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (500 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 324,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (500 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_500 :
    recurrence4Scalar0Main.coeff 500 =
      -(((271593725714991639041936092 * 10 ^ 70 +
        0588965966866370402089639858900842049008907321219211326671067024378365) * 10 ^ 70 +
        4988515097599614290657624135312657260759784346068141177532674793138371) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (500 - x)) = _
  rw [show 501 = 154 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 23 +
      324 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_500_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (501 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 325,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (501 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_501 :
    recurrence4Scalar0Main.coeff 501 =
      (((831476349648137871878782 * 10 ^ 70 +
        0527971676670104169135293628459269496683970377211790238845988537214368) * 10 ^ 70 +
        0735353671658219518730854882183301853091191250724441319059501799419864) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (501 - x)) = _
  rw [show 502 = 155 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 22 +
      325 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_501_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (502 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 326,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (502 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_502 :
    recurrence4Scalar0Main.coeff 502 =
      (((111383870854527271896 * 10 ^ 70 +
        3098370512639044110057437653998344215615102752199018471001554932929326) * 10 ^ 70 +
        3668091941155510159845922382414182732107879934269273987081517530199032) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (502 - x)) = _
  rw [show 503 = 156 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 21 +
      326 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_502_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (503 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 327,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (503 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_503 :
    recurrence4Scalar0Main.coeff 503 =
      -(((982467869763658345 * 10 ^ 70 +
        4807683039574172477440782351086424507438258956708159875881530946387860) * 10 ^ 70 +
        2129652152932336854031984318469278937949951487262685415324182547812308) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (503 - x)) = _
  rw [show 504 = 157 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 20 +
      327 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_503_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (504 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 328,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (504 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_504 :
    recurrence4Scalar0Main.coeff 504 =
      (((341034324197377 * 10 ^ 70 +
        3480963577618286711722423826104400450411616293879103236714001785936488) * 10 ^ 70 +
        9472851126708017188287836794705351494104225212833460581965021678761588) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (504 - x)) = _
  rw [show 505 = 158 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 19 +
      328 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_504_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (505 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 329,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (505 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_505 :
    recurrence4Scalar0Main.coeff 505 =
      (((239960294964 * 10 ^ 70 +
        3388356724097422917847729429920294502687176992689412570946125619058744) * 10 ^ 70 +
        6543913838644879080141815523292120042594037807708373209061900740901587) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (505 - x)) = _
  rw [show 506 = 159 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 18 +
      329 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_505_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (506 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 330,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (506 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_506 :
    recurrence4Scalar0Main.coeff 506 =
      -(((128144854 * 10 ^ 70 +
        4544562340722769248270921561454438172848350922427768285132479472075908) * 10 ^ 70 +
        8930362157418756993715882306483033487646881132751150433820378463322892) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (506 - x)) = _
  rw [show 507 = 160 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 17 +
      330 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_506_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_507_prefix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (507 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (507 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_507_suffix_zero :
    (∑ x ∈ Finset.range 331,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (507 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_507 :
    recurrence4Scalar0Main.coeff 507 =
      (((3287 * 10 ^ 70 +
        0555432940163478594368281621544716994119117776590400537827604896536447) * 10 ^ 70 +
        8511284157229327367109477490785914827208103441524093198913470416515540) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 508,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (507 - x)) = _
  rw [show 508 = 161 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 16 +
      331 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_507_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_507_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_508_prefix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (508 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (508 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_508_suffix_zero :
    (∑ x ∈ Finset.range 332,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (508 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_508 :
    recurrence4Scalar0Main.coeff 508 =
      (((4 * 10 ^ 70 +
        7375742970005438025343175459434391477722032433844007979405427149161312) * 10 ^ 70 +
        8082415335078839743704936214652504082288057621098424210612251780072551) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 509,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (508 - x)) = _
  rw [show 509 = 162 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 15 +
      332 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_508_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_508_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_509_prefix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (509 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (509 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_509_suffix_zero :
    (∑ x ∈ Finset.range 333,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (509 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_509 :
    recurrence4Scalar0Main.coeff 509 =
      -((4758397152911358331003546804314992405522174310234040518141558385453 * 10 ^ 70 +
        5833464846716507903226213951236004170067068496481336793066243163645679) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 510,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (509 - x)) = _
  rw [show 510 = 163 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 14 +
      333 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_509_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_509_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_510_prefix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (510 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (510 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_510_suffix_zero :
    (∑ x ∈ Finset.range 334,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (510 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_510 :
    recurrence4Scalar0Main.coeff 510 =
      -((60782999487503885584441959565739633590531439839587184048285096 * 10 ^ 70 +
        2903284980291318248167034241764188981722415018927465167630789934640857) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 511,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (510 - x)) = _
  rw [show 511 = 164 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 13 +
      334 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_510_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_510_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_511_prefix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (511 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (511 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_511_suffix_zero :
    (∑ x ∈ Finset.range 335,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (511 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_511 :
    recurrence4Scalar0Main.coeff 511 =
      ((15442178053861214722600298743718491566974627657848686709730 * 10 ^ 70 +
        7141087597575790478114591033590497496163096572851201775881852147980267) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 512,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (511 - x)) = _
  rw [show 512 = 165 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 12 +
      335 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_511_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_511_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
