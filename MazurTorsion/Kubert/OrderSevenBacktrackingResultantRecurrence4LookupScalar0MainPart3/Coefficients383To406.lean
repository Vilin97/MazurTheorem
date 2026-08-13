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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
