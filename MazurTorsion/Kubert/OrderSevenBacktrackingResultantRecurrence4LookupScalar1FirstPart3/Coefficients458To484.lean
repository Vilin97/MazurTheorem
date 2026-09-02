/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1FirstPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

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
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92

attribute [local simp]
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_210
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

attribute [local simp]
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_270
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

attribute [local simp]
  recurrence4B3A4_coeff_329
  recurrence4B3A4_coeff_330
  recurrence4B3A4_coeff_331
  recurrence4B3A4_coeff_332
  recurrence4B3A4_coeff_333
  recurrence4B3A4_coeff_334
  recurrence4B3A4_coeff_335
  recurrence4B3A4_coeff_336
  recurrence4B3A4_coeff_337
  recurrence4B3A4_coeff_338
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar1First_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (458 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (458 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_458 :
    recurrence4Scalar1First.coeff 458 =
      ((((2132243542734384572814 * 10 ^ 70 +
        0095559632074990518822021520760100107656389306835890825676817771918807) * 10 ^ 70 +
        8174746001840482059443722019331164335817674764591717684518017930741739) * 10 ^ 70 +
        4801224622222818968507843706865513630423555757543089259121069931705520) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (458 - x)) = _
  rw [show 459 = 116 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 29 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (459 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (459 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_459 :
    recurrence4Scalar1First.coeff 459 =
      -((((193522502780396037866 * 10 ^ 70 +
        1963715796112810753555359291974712810519623426833577793750181092421880) * 10 ^ 70 +
        7905502577504597271055172033922843240851940032542931171139119714446330) * 10 ^ 70 +
        0368200383517942887371042525223594009025564874467095489593637848589127) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (459 - x)) = _
  rw [show 460 = 117 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 28 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (460 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (460 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_460 :
    recurrence4Scalar1First.coeff 460 =
      ((((14212419137419108337 * 10 ^ 70 +
        9695700871707336731290203518699416363873888599934300625834890474017962) * 10 ^ 70 +
        0250101524949246312656394937335979202526947214319236174334509684110670) * 10 ^ 70 +
        7445113409975841187035929279529599670174795101157541820512141336719039) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (460 - x)) = _
  rw [show 461 = 118 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 27 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (461 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (461 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_461 :
    recurrence4Scalar1First.coeff 461 =
      -((((676851404585270119 * 10 ^ 70 +
        7840443534112595912269742626490249071864645151438706750184057188923552) * 10 ^ 70 +
        2192974062282935765059264487791625552457157242326650935854483735544035) * 10 ^ 70 +
        0925773428999474152130708287761097111176290935351311752893888589148976) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (461 - x)) = _
  rw [show 462 = 119 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 26 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (462 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (462 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_462 :
    recurrence4Scalar1First.coeff 462 =
      -((((11912040866373518 * 10 ^ 70 +
        0695352168599085227965797261491894755624677492542027686653972034912328) * 10 ^ 70 +
        9446472865477051714090608585872272304439870044352299236326944497148293) * 10 ^ 70 +
        9178772112991399311729588881281782253592531646044645164898588953389378) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (462 - x)) = _
  rw [show 463 = 120 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 25 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (463 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (463 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_463 :
    recurrence4Scalar1First.coeff 463 =
      ((((7505752630179668 * 10 ^ 70 +
        8132923136409812380882432574573295361438933779543328876523281816454607) * 10 ^ 70 +
        9569582394248842448515257527192357889041007241421626190820710753431079) * 10 ^ 70 +
        7485387521832000940994843110926755230304518594716887125798117949453049) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (463 - x)) = _
  rw [show 464 = 121 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 24 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (464 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (464 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_464 :
    recurrence4Scalar1First.coeff 464 =
      -((((1051587746530481 * 10 ^ 70 +
        6642066116914551698014747445332981779492648726749514317719731183257097) * 10 ^ 70 +
        3655215641534133734180451301289596355979498733962383966800480618642122) * 10 ^ 70 +
        6963898127108625395943715702804955690273740678011760279952724870041738) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (464 - x)) = _
  rw [show 465 = 122 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 23 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (465 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (465 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_465 :
    recurrence4Scalar1First.coeff 465 =
      ((((98324696441297 * 10 ^ 70 +
        5770371919002193806019455730853916213216307840003468961347465573413406) * 10 ^ 70 +
        0371803054296277553906049431805952053817989785441755407462628640307215) * 10 ^ 70 +
        9097662953945287228608143892445236766989545275054061676801122829918671) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (465 - x)) = _
  rw [show 466 = 123 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 22 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (466 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (466 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_466 :
    recurrence4Scalar1First.coeff 466 =
      -((((6512942407355 * 10 ^ 70 +
        2769845278009641941232057209533571348808156165142776413910496817455634) * 10 ^ 70 +
        7838036202333294830511908875073989864384625028205504939629908128273718) * 10 ^ 70 +
        9761718271454401282496561727312513151148348881319686504169133680784012) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (466 - x)) = _
  rw [show 467 = 124 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 21 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (467 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (467 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_467 :
    recurrence4Scalar1First.coeff 467 =
      ((((246685725995 * 10 ^ 70 +
        9782294656210889165779012059850003265819588907425359035645920064772678) * 10 ^ 70 +
        0729702618218854052250181233222761894194959877402674978663365328511930) * 10 ^ 70 +
        0430911623565056349484579205664371419539754598065375536565490225746678) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (467 - x)) = _
  rw [show 468 = 125 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 20 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_467_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (468 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (468 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_468 :
    recurrence4Scalar1First.coeff 468 =
      ((((5721656605 * 10 ^ 70 +
        1100155284601409499295615931399544311460460210746880980393329911921158) * 10 ^ 70 +
        6086464204440646651378579191280326696949057013710873943671586053413939) * 10 ^ 70 +
        5317869981542624221102032235780859927037027740311007536680075519812673) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (468 - x)) = _
  rw [show 469 = 126 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 19 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_468_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (469 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (469 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_469 :
    recurrence4Scalar1First.coeff 469 =
      -((((1848757159 * 10 ^ 70 +
        8581478102623126944909126193400723001732519797788866487834664465865696) * 10 ^ 70 +
        1904948119900124714321145304629001300152725140923198171454918619705622) * 10 ^ 70 +
        2598203703898251469298661628860835129705606298401355850743010667468023) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (469 - x)) = _
  rw [show 470 = 127 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 18 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_469_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (470 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (470 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_470 :
    recurrence4Scalar1First.coeff 470 =
      ((((168001804 * 10 ^ 70 +
        1115948583582087980595709174820757600512644434220881750702070613507374) * 10 ^ 70 +
        5042122668749876483382556554538485167508046169894864941091651824245941) * 10 ^ 70 +
        2684307540427718912150874669594667957143295177215770483844037044602444) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (470 - x)) = _
  rw [show 471 = 128 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 17 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_470_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (471 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (471 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_471 :
    recurrence4Scalar1First.coeff 471 =
      -((((9118060 * 10 ^ 70 +
        9342227595684593400402307317227234097963136100007298318148974102959610) * 10 ^ 70 +
        8774388019672774075945321629722650088872011382725834601900199882447846) * 10 ^ 70 +
        8390517262836699892005986349292548573434817421129071603324631042358093) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (471 - x)) = _
  rw [show 472 = 129 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 16 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_471_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (472 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (472 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_472 :
    recurrence4Scalar1First.coeff 472 =
      ((((250753 * 10 ^ 70 +
        3576167343717293255590845073319369596156696085549696888168128784491337) * 10 ^ 70 +
        6337801992601095663716661377454802666038498678003979181044719398897719) * 10 ^ 70 +
        8706596396931308320165707700733997131308538346579616356342163970518770) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (472 - x)) = _
  rw [show 473 = 130 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 15 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_472_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (473 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (473 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_473 :
    recurrence4Scalar1First.coeff 473 =
      ((((5152 * 10 ^ 70 +
        4629215070575844341531869567195676171973212241552904231924124027982109) * 10 ^ 70 +
        2339402797066435354588860758594073530111982849485952465932757236775767) * 10 ^ 70 +
        0832754560011436992777257759801617948668106693509484388723057853630059) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (473 - x)) = _
  rw [show 474 = 131 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 14 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_473_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (474 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (474 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_474 :
    recurrence4Scalar1First.coeff 474 =
      -((((907 * 10 ^ 70 +
        3892103941242784660790793792271454217500950504734630219468083392677393) * 10 ^ 70 +
        3315513429774162729326007481856705598593856723148427702755844833398861) * 10 ^ 70 +
        2459705604167789154231421864408515891330735756957614555435043397585154) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (474 - x)) = _
  rw [show 475 = 132 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 13 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_474_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (475 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (475 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_475 :
    recurrence4Scalar1First.coeff 475 =
      ((((43 * 10 ^ 70 +
        9145457361110369285285598407383734029994604838224810212468064338038981) * 10 ^ 70 +
        9757626508640410888086343859175714653552671280097915540537851705674661) * 10 ^ 70 +
        7384817694761147712406002580360888523503755413483773801856644726452059) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (475 - x)) = _
  rw [show 476 = 133 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 12 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_475_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (476 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (476 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_476 :
    recurrence4Scalar1First.coeff 476 =
      -(((8630150453406617890951592861916501457947717440448650460528922550882542 * 10 ^ 70 +
        4818917122128416410541703990802810224215818093644452260194961421212525) * 10 ^ 70 +
        3892966053240573167678430150598276320841003350740399618414402793669086) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (476 - x)) = _
  rw [show 477 = 134 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 11 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_476_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (477 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (477 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_477 :
    recurrence4Scalar1First.coeff 477 =
      -(((150046024558216634430908223171364108976208871546421372433022246795929 * 10 ^ 70 +
        3235358425524859425965787435739776007346029812987850108680276000372997) * 10 ^ 70 +
        8036593994838664854735553309337479395329438156661659870107929629737132) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (477 - x)) = _
  rw [show 478 = 135 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 10 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_477_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (478 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (478 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_478 :
    recurrence4Scalar1First.coeff 478 =
      (((12573588951064079787261767941931747931658333277899406928643917323541 * 10 ^ 70 +
        1711822745272751899518154444096001592574536568529803826789308779129857) * 10 ^ 70 +
        5034496875789545957806497511695292989450888670229914849290090247092241) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (478 - x)) = _
  rw [show 479 = 136 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 9 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (479 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (479 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_479 :
    recurrence4Scalar1First.coeff 479 =
      -(((209589070113555646023053802508960172284259072441423819082912659269 * 10 ^ 70 +
        9808951919185102112870310364838558005402348112008968990126419937727174) * 10 ^ 70 +
        9552805656224898631890912288081250600410556679478307038671096207174594) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (479 - x)) = _
  rw [show 480 = 137 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 8 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (480 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (480 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_480 :
    recurrence4Scalar1First.coeff 480 =
      -(((2735167132955559180408905565668959476472212069394223692449034301 * 10 ^ 70 +
        6991259780557913546576044309586145317880981014654882940479947575728439) * 10 ^ 70 +
        8327233164145774560302455203684255160387230409025223626929362358899040) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (480 - x)) = _
  rw [show 481 = 138 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 7 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (481 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (481 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_481 :
    recurrence4Scalar1First.coeff 481 =
      (((109465818727350610099543711145551895500393979789267722581891644 * 10 ^ 70 +
        5567175835700291509826763743557244764571971732268835121470229368364840) * 10 ^ 70 +
        7697838799469164700188159985333149206519416123383211906715312019038224) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (481 - x)) = _
  rw [show 482 = 139 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 6 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (482 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (482 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_482 :
    recurrence4Scalar1First.coeff 482 =
      (((114098085597399545196246396470584643239447369472257458145459 * 10 ^ 70 +
        5032325164817294609210907539104204401283829184808244114883447129685129) * 10 ^ 70 +
        9878117894627160450143866359795819025252487488571510836420120211088852) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (482 - x)) = _
  rw [show 483 = 140 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 5 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (483 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (483 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_483 :
    recurrence4Scalar1First.coeff 483 =
      -(((21079716471050467252194432305119714207422246558881626358805 * 10 ^ 70 +
        6221531323816400268390130777239976220840111283647786156954682939299440) * 10 ^ 70 +
        5437369894713045825081640917492565368317420251974367493945378033181106) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (483 - x)) = _
  rw [show 484 = 141 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 4 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1First_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (484 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (484 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_484 :
    recurrence4Scalar1First.coeff 484 =
      -(((21877908131638057693534703529642911212818323599467611714 * 10 ^ 70 +
        6372418314912375880260698354550874261220095088798311022138481575565020) * 10 ^ 70 +
        1899597889143954578408806716242437783853556039842641760513144445299563) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (484 - x)) = _
  rw [show 485 = 142 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 3 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1First_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
