/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B2_coeff_10
  recurrence4B2_coeff_100
  recurrence4B2_coeff_101
  recurrence4B2_coeff_102
  recurrence4B2_coeff_103
  recurrence4B2_coeff_104
  recurrence4B2_coeff_105
  recurrence4B2_coeff_106
  recurrence4B2_coeff_107
  recurrence4B2_coeff_108
  recurrence4B2_coeff_109
  recurrence4B2_coeff_11
  recurrence4B2_coeff_110
  recurrence4B2_coeff_111
  recurrence4B2_coeff_112
  recurrence4B2_coeff_113
  recurrence4B2_coeff_114
  recurrence4B2_coeff_115
  recurrence4B2_coeff_116
  recurrence4B2_coeff_117
  recurrence4B2_coeff_118
  recurrence4B2_coeff_119
  recurrence4B2_coeff_12
  recurrence4B2_coeff_120
  recurrence4B2_coeff_121
  recurrence4B2_coeff_122
  recurrence4B2_coeff_123
  recurrence4B2_coeff_124
  recurrence4B2_coeff_125
  recurrence4B2_coeff_126
  recurrence4B2_coeff_127
  recurrence4B2_coeff_128
  recurrence4B2_coeff_129
  recurrence4B2_coeff_13
  recurrence4B2_coeff_130
  recurrence4B2_coeff_131
  recurrence4B2_coeff_132
  recurrence4B2_coeff_133
  recurrence4B2_coeff_134
  recurrence4B2_coeff_135
  recurrence4B2_coeff_136
  recurrence4B2_coeff_137
  recurrence4B2_coeff_138
  recurrence4B2_coeff_139
  recurrence4B2_coeff_14
  recurrence4B2_coeff_140
  recurrence4B2_coeff_141
  recurrence4B2_coeff_142
  recurrence4B2_coeff_143
  recurrence4B2_coeff_144
  recurrence4B2_coeff_145
  recurrence4B2_coeff_146
  recurrence4B2_coeff_147
  recurrence4B2_coeff_148
  recurrence4B2_coeff_149
  recurrence4B2_coeff_15
  recurrence4B2_coeff_150
  recurrence4B2_coeff_151
  recurrence4B2_coeff_152
  recurrence4B2_coeff_153
  recurrence4B2_coeff_154
  recurrence4B2_coeff_155
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157

attribute [local simp]
  recurrence4B2_coeff_158
  recurrence4B2_coeff_159
  recurrence4B2_coeff_16
  recurrence4B2_coeff_160
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167
  recurrence4B2_coeff_168
  recurrence4B2_coeff_17
  recurrence4B2_coeff_18
  recurrence4B2_coeff_19
  recurrence4B2_coeff_20
  recurrence4B2_coeff_21
  recurrence4B2_coeff_22
  recurrence4B2_coeff_23
  recurrence4B2_coeff_24
  recurrence4B2_coeff_25
  recurrence4B2_coeff_26
  recurrence4B2_coeff_27
  recurrence4B2_coeff_28
  recurrence4B2_coeff_29
  recurrence4B2_coeff_30
  recurrence4B2_coeff_31
  recurrence4B2_coeff_32
  recurrence4B2_coeff_33
  recurrence4B2_coeff_34
  recurrence4B2_coeff_35
  recurrence4B2_coeff_36
  recurrence4B2_coeff_37
  recurrence4B2_coeff_38
  recurrence4B2_coeff_39
  recurrence4B2_coeff_4
  recurrence4B2_coeff_40
  recurrence4B2_coeff_41
  recurrence4B2_coeff_42
  recurrence4B2_coeff_43
  recurrence4B2_coeff_44
  recurrence4B2_coeff_45
  recurrence4B2_coeff_46
  recurrence4B2_coeff_47
  recurrence4B2_coeff_48
  recurrence4B2_coeff_49
  recurrence4B2_coeff_5
  recurrence4B2_coeff_50
  recurrence4B2_coeff_51
  recurrence4B2_coeff_52
  recurrence4B2_coeff_53
  recurrence4B2_coeff_54
  recurrence4B2_coeff_55
  recurrence4B2_coeff_56
  recurrence4B2_coeff_57
  recurrence4B2_coeff_58
  recurrence4B2_coeff_59
  recurrence4B2_coeff_6
  recurrence4B2_coeff_60
  recurrence4B2_coeff_61
  recurrence4B2_coeff_62
  recurrence4B2_coeff_63
  recurrence4B2_coeff_64
  recurrence4B2_coeff_65

attribute [local simp]
  recurrence4B2_coeff_66
  recurrence4B2_coeff_67
  recurrence4B2_coeff_68
  recurrence4B2_coeff_69
  recurrence4B2_coeff_7
  recurrence4B2_coeff_70
  recurrence4B2_coeff_71
  recurrence4B2_coeff_72
  recurrence4B2_coeff_73
  recurrence4B2_coeff_74
  recurrence4B2_coeff_75
  recurrence4B2_coeff_76
  recurrence4B2_coeff_77
  recurrence4B2_coeff_78
  recurrence4B2_coeff_79
  recurrence4B2_coeff_8
  recurrence4B2_coeff_80
  recurrence4B2_coeff_81
  recurrence4B2_coeff_82
  recurrence4B2_coeff_83
  recurrence4B2_coeff_84
  recurrence4B2_coeff_85
  recurrence4B2_coeff_86
  recurrence4B2_coeff_87
  recurrence4B2_coeff_88
  recurrence4B2_coeff_89
  recurrence4B2_coeff_9
  recurrence4B2_coeff_90
  recurrence4B2_coeff_91
  recurrence4B2_coeff_92
  recurrence4B2_coeff_93
  recurrence4B2_coeff_94
  recurrence4B2_coeff_95
  recurrence4B2_coeff_96
  recurrence4B2_coeff_97
  recurrence4B2_coeff_98
  recurrence4B2_coeff_99
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208

attribute [local simp]
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

attribute [local simp]
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
  recurrence4QuotientConstant_coeff_331
  recurrence4QuotientConstant_coeff_332
  recurrence4QuotientConstant_coeff_333
  recurrence4QuotientConstant_coeff_334
  recurrence4QuotientConstant_coeff_335
  recurrence4QuotientConstant_coeff_336

attribute [local simp]
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

private theorem recurrence4Scalar2Second_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (350 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_350 :
    recurrence4Scalar2Second.coeff 350 =
      (((((24613942 * 10 ^ 70 +
        4649631578604410694649281217779524828402434776427660313728057354505687) * 10 ^ 70 +
        5632680287441792894043102607565805193914882827480979718297425680760927) * 10 ^ 70 +
        3439348255022174362363318426678581146464632116869128693880989434776911) * 10 ^ 70 +
        1654288979433561018557406658666373906253171104332132962660687189158890) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (350 - x)) = _
  rw [show 351 = 4 +
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
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (351 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_351 :
    recurrence4Scalar2Second.coeff 351 =
      -(((((8854950 * 10 ^ 70 +
        8114682616149435569230831252835426064573280635912367458351791638072171) * 10 ^ 70 +
        2667045885320154054631821785724319340378865358304197894397458320492174) * 10 ^ 70 +
        7371526824700755186467198871071076708911828396093121506922746103028287) * 10 ^ 70 +
        4930178604013106252909718829966754787561634782896608133553110181782716) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (351 - x)) = _
  rw [show 352 = 5 +
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
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 4 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (352 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_352 :
    recurrence4Scalar2Second.coeff 352 =
      (((((3167829 * 10 ^ 70 +
        4275485430866934025278209388058009233880834624899422972592529407836257) * 10 ^ 70 +
        0133839849501168073003797596112697819143602299349061268823675410396952) * 10 ^ 70 +
        9538217106008092583283729842554776343101953894816515778888858799200125) * 10 ^ 70 +
        7302432336028759171537876094345265588602789236184058235436252711787848) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (352 - x)) = _
  rw [show 353 = 6 +
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
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 3 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (353 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_353 :
    recurrence4Scalar2Second.coeff 353 =
      -(((((1140362 * 10 ^ 70 +
        1532273285067526731115977772352714551447338116026082575382916821416051) * 10 ^ 70 +
        6607909585660839062793242235698929292806921138748912110147168885731778) * 10 ^ 70 +
        3240449305166716821478222243094579574275424307810772808901604845203497) * 10 ^ 70 +
        1545523562122321602339616411655562891051307486628477971028693981357421) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (353 - x)) = _
  rw [show 354 = 7 +
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
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 2 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (354 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_354 :
    recurrence4Scalar2Second.coeff 354 =
      (((((419706 * 10 ^ 70 +
        0451502378994628404887624285703200862889449433384398944060275028391831) * 10 ^ 70 +
        7848857926668490877928775477993281934257854640569102927399450968596707) * 10 ^ 70 +
        0371915386526935404407220774990873634212304845660622779089922634504558) * 10 ^ 70 +
        7617434634673666297408380763453726147355283069235184735609020891770277) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (354 - x)) = _
  rw [show 355 = 8 +
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
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 1 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (355 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_355 :
    recurrence4Scalar2Second.coeff 355 =
      -(((((160660 * 10 ^ 70 +
        3959082253508613362737865208393491433954096784706141948818796033332635) * 10 ^ 70 +
        6596236763267337742679927143975313832955682897107706832762166130386531) * 10 ^ 70 +
        0091317592033438728179293270120483045244924974206486566743751549648644) * 10 ^ 70 +
        3670825561925666345249726738848885158668553213546080925893322617167980) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (355 - x)) = _
  rw [show 356 = 9 +
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
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (356 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_356 :
    recurrence4Scalar2Second.coeff 356 =
      (((((64746 * 10 ^ 70 +
        7663838124002054245662726956171545139771433818872341162732720639706092) * 10 ^ 70 +
        7858838695269292353928998944421584399747182760778517733739249626309380) * 10 ^ 70 +
        5354011740640029902150209902889069779917588330117604363659350457844736) * 10 ^ 70 +
        6741499856560760710109967932857496797442776979703130214761814177338961) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (356 - x)) = _
  rw [show 357 = 10 +
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
    rw [show 219 = 31 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (357 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_357 :
    recurrence4Scalar2Second.coeff 357 =
      -(((((27500 * 10 ^ 70 +
        3638579313436428947342603418395780173378249578303323246596933821467329) * 10 ^ 70 +
        7533745893989557654845352123269105068277997411420973471095841055197834) * 10 ^ 70 +
        3022355946274695084521240036019577533244131635328257096742003209595107) * 10 ^ 70 +
        8161769118556884419055228440457322270814683910684161256395361727695438) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (357 - x)) = _
  rw [show 358 = 11 +
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
    rw [show 219 = 30 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (358 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_358 :
    recurrence4Scalar2Second.coeff 358 =
      (((((12178 * 10 ^ 70 +
        9262337281236750491807883685589110398287586642687252892885863569711373) * 10 ^ 70 +
        6464456777063091583841617325489120449324510971565186139230099664382078) * 10 ^ 70 +
        2087447999659611911933784726526188971098776363358749744444668938036909) * 10 ^ 70 +
        6811437315404401964661743820566768267695913042161028785254764669319015) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (358 - x)) = _
  rw [show 359 = 12 +
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
    rw [show 219 = 29 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (359 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_359 :
    recurrence4Scalar2Second.coeff 359 =
      -(((((5528 * 10 ^ 70 +
        3609196222633524870789512590231333535113835876604064314832844242986336) * 10 ^ 70 +
        9570577207278679287722922913647365738826470448536121456490255762284994) * 10 ^ 70 +
        8179058803557300326272546234500699589789921800273136344777990322515155) * 10 ^ 70 +
        9934407022674337752953654334127046865816020800123308324381402601946686) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (359 - x)) = _
  rw [show 360 = 13 +
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
    rw [show 219 = 28 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (360 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_360 :
    recurrence4Scalar2Second.coeff 360 =
      (((((2528 * 10 ^ 70 +
        9391257315151386142532010863348043555875222958441573928164909629536171) * 10 ^ 70 +
        8055610094551421714085553120084634096522519876504863996303408005131673) * 10 ^ 70 +
        2743017791513554909427283077551012016071626009295920589257390665881436) * 10 ^ 70 +
        2565344324076972168347101138421614056106384747689434791113892094175396) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (360 - x)) = _
  rw [show 361 = 14 +
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
    rw [show 219 = 27 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (361 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_361 :
    recurrence4Scalar2Second.coeff 361 =
      -(((((1150 * 10 ^ 70 +
        5306018912493641809635683971246377437933491339348694914382768833083684) * 10 ^ 70 +
        4511511787608956000946934333280116180321983326921038439909878743659172) * 10 ^ 70 +
        8992395745835156685722533588041451227262115116251585355218465737238975) * 10 ^ 70 +
        3670528924338199864275615251901204088329815132076066859827383703933830) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (361 - x)) = _
  rw [show 362 = 15 +
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
    rw [show 219 = 26 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (362 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_362 :
    recurrence4Scalar2Second.coeff 362 =
      (((((515 * 10 ^ 70 +
        9304596066441931816268954318287811960194891210132274310610876954698625) * 10 ^ 70 +
        4956091204336155641580709467287804151750179995676270921251113941631772) * 10 ^ 70 +
        7715545444484516768393165078538044335713049457366570071771349358887631) * 10 ^ 70 +
        4674948876737023654886364191378256806307941408936699529781013712262950) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (362 - x)) = _
  rw [show 363 = 16 +
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
    rw [show 219 = 25 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (363 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_363 :
    recurrence4Scalar2Second.coeff 363 =
      -(((((226 * 10 ^ 70 +
        7715368189517989667968101000364125693186158005703156044778617512339877) * 10 ^ 70 +
        9311007445330797416947454172333403438213386912224447634257984094240954) * 10 ^ 70 +
        7608684419794467229772845578947841712900331974356554960340726577246669) * 10 ^ 70 +
        9300770643005517207633726943649712937164914878864683054314653970921212) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (363 - x)) = _
  rw [show 364 = 17 +
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
    rw [show 219 = 24 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (364 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_364 :
    recurrence4Scalar2Second.coeff 364 =
      (((((97 * 10 ^ 70 +
        3687629274417532545141351887426298570056085424054336815894858243691725) * 10 ^ 70 +
        5132733775808842632517239535182196220928296446711585496454301831933412) * 10 ^ 70 +
        4731137899047094152981579676195564835128498529275687000321597280575257) * 10 ^ 70 +
        2055477771330187406605471252277674658746826390388633527990451055129339) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (364 - x)) = _
  rw [show 365 = 18 +
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
    rw [show 219 = 23 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (365 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_365 :
    recurrence4Scalar2Second.coeff 365 =
      -(((((40 * 10 ^ 70 +
        7542610115178977853011827445240182322865817530526743654231639268163725) * 10 ^ 70 +
        5110008771740639425544160339760744892067933574783933093534549155499219) * 10 ^ 70 +
        2739383285079969524182495910039123891351499874892851151897676777304035) * 10 ^ 70 +
        5529196986506026736887405057843302195570809246432916788075233287486216) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (365 - x)) = _
  rw [show 366 = 19 +
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
    rw [show 219 = 22 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (366 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_366 :
    recurrence4Scalar2Second.coeff 366 =
      (((((16 * 10 ^ 70 +
        6043545246945017147781475828708791387907120973046048315974345681792248) * 10 ^ 70 +
        6972123852828869964880141880053206220131340650344402114698609880525131) * 10 ^ 70 +
        7686730175037654104048735644022273488384283632896549829288101482447585) * 10 ^ 70 +
        5543070223222153078304535300360150102693050284636831023676142527950208) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (366 - x)) = _
  rw [show 367 = 20 +
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
    rw [show 219 = 21 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (367 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_367 :
    recurrence4Scalar2Second.coeff 367 =
      -(((((6 * 10 ^ 70 +
        5772642657110858163351292263148777373612636437863702791768280588992675) * 10 ^ 70 +
        1774576021211250579198545503901580458652210369119675631243624787970901) * 10 ^ 70 +
        8693277069700709217663003503327678870617710084939742606440072566691159) * 10 ^ 70 +
        0102204491967438636222404321569260453427741376652299741089928339788543) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (367 - x)) = _
  rw [show 368 = 21 +
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
    rw [show 219 = 20 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (368 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_368 :
    recurrence4Scalar2Second.coeff 368 =
      (((((2 * 10 ^ 70 +
        5299182972517814490792503779387711620264033771927071846433688573014120) * 10 ^ 70 +
        3985691218669222810474166477009352067775991964985260786226028162931064) * 10 ^ 70 +
        9615067869730173195077943051464282672547798458089970153168240845204700) * 10 ^ 70 +
        7555664353920072760278469805418631288140631750739364979233008735377214) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (368 - x)) = _
  rw [show 369 = 22 +
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
    rw [show 219 = 19 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (369 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_369 :
    recurrence4Scalar2Second.coeff 369 =
      -((((9435458559893092415883854746688688989717238944575628913231885475046567 * 10 ^ 70 +
        8121398216074356732686778275179725380062088909593527969024518182341260) * 10 ^ 70 +
        3517841871126346126807035494309986010083325325873092498463444006945227) * 10 ^ 70 +
        0858467265831738011904806403478642664707446630184930569502230660574123) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (369 - x)) = _
  rw [show 370 = 23 +
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
    rw [show 219 = 18 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (370 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_370 :
    recurrence4Scalar2Second.coeff 370 =
      ((((3405496360603659868909366727457203082276886722668068719815467489306059 * 10 ^ 70 +
        9353450597712886727732545395731705353513835392947733880231480169630789) * 10 ^ 70 +
        6457106139589576622522939313880223289982221240641829229198196388971642) * 10 ^ 70 +
        9622671484238111488836155867651408399262390130601174200956262449928241) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (370 - x)) = _
  rw [show 371 = 24 +
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
    rw [show 219 = 17 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (371 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_371 :
    recurrence4Scalar2Second.coeff 371 =
      -((((1186392539466391650923984287822092345503922155314499970260161022628613 * 10 ^ 70 +
        1712163971997937434859857298797395259641599416661134254426160685375879) * 10 ^ 70 +
        0546901783139054670765777342932235090255441525982485304172363015016870) * 10 ^ 70 +
        8417875094460636767145244188733556143792143766770227247127144168381642) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (371 - x)) = _
  rw [show 372 = 25 +
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
    rw [show 219 = 16 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (372 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_372 :
    recurrence4Scalar2Second.coeff 372 =
      ((((397489113425347366061235232817874375687561252344874596656073870052741 * 10 ^ 70 +
        2012575584898280690586682833964834216431500029920817955277477694378573) * 10 ^ 70 +
        0840803541265603297412087230492954731341498891113496241287734541232162) * 10 ^ 70 +
        7900726438017781087046298400841922576880225575928100770930425327275073) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (372 - x)) = _
  rw [show 373 = 26 +
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
    rw [show 219 = 15 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (373 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_373 :
    recurrence4Scalar2Second.coeff 373 =
      -((((127400253956792869856064953187608958370253417813907931144198896448211 * 10 ^ 70 +
        1654281418417781322351254925694016146726704016602849388150129592157927) * 10 ^ 70 +
        9626092243284805006931823682727843460983935974557539242744889453659014) * 10 ^ 70 +
        3530435699680555902711901895062748485046762472594144627828376264091599) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (373 - x)) = _
  rw [show 374 = 27 +
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
    rw [show 219 = 14 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (374 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_374 :
    recurrence4Scalar2Second.coeff 374 =
      ((((38746287200054783452990775342142074950576510439388268047873089631692 * 10 ^ 70 +
        7385384456487308305582994287143576348770899611595723332293739099893086) * 10 ^ 70 +
        4600534531811854807975486321982327024999338746289728681569400214048769) * 10 ^ 70 +
        9886105921776051443113267618884566080055153155507889420525831964333995) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (374 - x)) = _
  rw [show 375 = 28 +
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
    rw [show 219 = 13 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (375 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_375 :
    recurrence4Scalar2Second.coeff 375 =
      -((((11031326007482652174101316398512031289854710545930302167470799403466 * 10 ^ 70 +
        4172534630482859021254751331607828902922254224413171919670019053351636) * 10 ^ 70 +
        0473383393893092063288730786319901067980036864383886785072179710699320) * 10 ^ 70 +
        3634132265929668452266425077527669295523632784530380211232977013625119) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (375 - x)) = _
  rw [show 376 = 29 +
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
  rw [recurrence4Scalar2Second_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (376 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_376 :
    recurrence4Scalar2Second.coeff 376 =
      ((((2866436238966211743624707332649774414048681855047779624432399898452 * 10 ^ 70 +
        3501159744116792207837699895568569177637301731231751184917858129285892) * 10 ^ 70 +
        8186762604529151819325627828162280681178478229804952056433756488982587) * 10 ^ 70 +
        8323879504293500523021286820246823071164188922398234789103475052744881) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (376 - x)) = _
  rw [show 377 = 30 +
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
  rw [recurrence4Scalar2Second_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (377 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_377 :
    recurrence4Scalar2Second.coeff 377 =
      -((((641589307720151358379197939887154115751814885516822935665743961199 * 10 ^ 70 +
        2147069318885751784606857433363673743145670978433986811768448750318638) * 10 ^ 70 +
        3654538403647968576463922659190850551925294708612105403484626390201935) * 10 ^ 70 +
        2433376644231585221056197699321742355528338806421784513033920976545336) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (377 - x)) = _
  rw [show 378 = 31 +
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
  rw [recurrence4Scalar2Second_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (378 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_378 :
    recurrence4Scalar2Second.coeff 378 =
      ((((101910038470230221388909107853010003903697740454372911409278511451 * 10 ^ 70 +
        9076304575100684019141382016470475980396146292407589420870164111106365) * 10 ^ 70 +
        9191814845239994759421359179320992686842836460226459080784730337672685) * 10 ^ 70 +
        1314407451031569951802591119272931546867199369754227343695462784971586) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (378 - x)) = _
  rw [show 379 = 32 +
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
  rw [recurrence4Scalar2Second_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (379 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_379 :
    recurrence4Scalar2Second.coeff 379 =
      ((((3232674094570134230649982401533658000771335464226595062564308547 * 10 ^ 70 +
        7277775461132292420610139422852948295504734475709468583246036031496749) * 10 ^ 70 +
        4692030871063106133144602369172829576569821399933250971314276258182054) * 10 ^ 70 +
        3116916655400115650164387936727939153807105915893229820242253698499871) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (379 - x)) = _
  rw [show 380 = 33 +
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
  rw [recurrence4Scalar2Second_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (380 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_380 :
    recurrence4Scalar2Second.coeff 380 =
      -((((12682561106500804334087886884304476355308494975724294337946199973 * 10 ^ 70 +
        0833885705036375504670056573312697289202025959271210100622692227739813) * 10 ^ 70 +
        8582536352973966961007801180930765529784276058941360071262786723405016) * 10 ^ 70 +
        9788734477238993292251524272672854188244958606459172042856012302593884) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (380 - x)) = _
  rw [show 381 = 34 +
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
  rw [recurrence4Scalar2Second_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (381 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_381 :
    recurrence4Scalar2Second.coeff 381 =
      ((((7657637224789611426253233958216835201447942880005507303442540877 * 10 ^ 70 +
        8051070789157107192568227119287835625025428332102117290416387760292831) * 10 ^ 70 +
        6482157911905972949266656773418537171434664066767584104406092002653718) * 10 ^ 70 +
        8489727452110319375526891580134658217906963434192298887064887043723874) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (381 - x)) = _
  rw [show 382 = 35 +
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
  rw [recurrence4Scalar2Second_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (382 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_382 :
    recurrence4Scalar2Second.coeff 382 =
      -((((3531736959837448561144613833429876426914158883714264728650248080 * 10 ^ 70 +
        6606920218733610210322731864168317904556778479889414331913464195517366) * 10 ^ 70 +
        1989296427028677133328814259958175712541458406993044508753523521917897) * 10 ^ 70 +
        5280543042353327144289010326515685150285196350193609286271413252670636) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (382 - x)) = _
  rw [show 383 = 36 +
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
  rw [recurrence4Scalar2Second_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (383 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_383 :
    recurrence4Scalar2Second.coeff 383 =
      ((((1458353384009747673508190427475574535747738286373089200714715448 * 10 ^ 70 +
        5074279428695294332535596573250562472895356549242655312767033272031048) * 10 ^ 70 +
        9716412564365979466824369676970876580771751402259930896775966777587362) * 10 ^ 70 +
        8565441354949478930602428265965445143416420997139259037793290936021776) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (383 - x)) = _
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
    rw [show 219 = 4 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (384 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_384 :
    recurrence4Scalar2Second.coeff 384 =
      -((((572866453725109364660534873595666603877569989322109529642385050 * 10 ^ 70 +
        7960928795072835059049961031732033214631516033908646577027392542789426) * 10 ^ 70 +
        4851255533451174616215778958034791413008866129162723778688630788006926) * 10 ^ 70 +
        2135152591700813627800044647321805197448623418023206947523858610934389) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (384 - x)) = _
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
    rw [show 219 = 3 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (385 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_385 :
    recurrence4Scalar2Second.coeff 385 =
      ((((221541906568022910328782828204855652543587787703836556527978735 * 10 ^ 70 +
        9636399113114612401177304860495847943447131965172274671381581378957134) * 10 ^ 70 +
        0021960354497527806954473231993647969307829581833315483524164919394986) * 10 ^ 70 +
        1588872058666562161790894921306367187865527634048052983704626316536295) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (385 - x)) = _
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
    rw [show 219 = 2 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (386 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_386 :
    recurrence4Scalar2Second.coeff 386 =
      -((((86123164768638926119337241488850060982765125393158799034028503 * 10 ^ 70 +
        8912109029831532328895618326694623872990123497316821325691016004535397) * 10 ^ 70 +
        6971681991010189867620725022314556287005497364318072276632581599105420) * 10 ^ 70 +
        5981605274293695764839045045288056004651829953583827091687668043201679) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (386 - x)) = _
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
    rw [show 219 = 1 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (387 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_387 :
    recurrence4Scalar2Second.coeff 387 =
      ((((33967173546214728006481535548419572644839133153944182231965266 * 10 ^ 70 +
        7397769935470578391273343490823028907283239085361998057601212102157448) * 10 ^ 70 +
        9936970858830507300865061790007537550671789204901025466039542469692346) * 10 ^ 70 +
        8884399103184348466707357093824079527283797850735871991160864728049699) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (387 - x)) = _
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
  rw [recurrence4Scalar2Second_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (388 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_388 :
    recurrence4Scalar2Second.coeff 388 =
      -((((13576916023994189641348185016448416151032315513082225240719304 * 10 ^ 70 +
        8331577783040656383690535035758970535259355421780434666587898927451966) * 10 ^ 70 +
        4200508705953105195422447513422663406061557823104666929137887849016599) * 10 ^ 70 +
        7674093305070051175904150062160320212376201957817000273057262638380678) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (388 - x)) = _
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
    rw [show 251 = 31 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (389 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_389 :
    recurrence4Scalar2Second.coeff 389 =
      ((((5456454076756558736551338006065591566850669462847647556347764 * 10 ^ 70 +
        5755774997135084964525092416792235665683209137281520958321453620281590) * 10 ^ 70 +
        8357519871859963253220915459936628382756919171233408596927199698312886) * 10 ^ 70 +
        5974599165649867528624387092548679892716038621853611434866522341200971) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (389 - x)) = _
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
    rw [show 251 = 30 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (390 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_390 :
    recurrence4Scalar2Second.coeff 390 =
      -((((2182350467065840974437178167393655296814285928431296083564457 * 10 ^ 70 +
        3100096784211781434153689546369348117253636186179038830393280805797164) * 10 ^ 70 +
        2152776392337291553477780818746451988000415206256336663845479493682482) * 10 ^ 70 +
        7561285562806096412943182547517147052995093494440969129716782023371577) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (390 - x)) = _
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
    rw [show 251 = 29 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (391 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_391 :
    recurrence4Scalar2Second.coeff 391 =
      ((((860501029053374203153262904962510471444677213145974481026124 * 10 ^ 70 +
        9037383145515909866568872799505529004097496074769360263119041860084704) * 10 ^ 70 +
        5441963860614017093649468002189460040582090835790876342764414610590665) * 10 ^ 70 +
        9857549398610940302541232912661262935402525617145235761923251795600156) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (391 - x)) = _
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
    rw [show 251 = 28 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (392 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_392 :
    recurrence4Scalar2Second.coeff 392 =
      -((((332078747524859340628892875600211153125208851427410501958346 * 10 ^ 70 +
        1599850824796547213538935042171430583642167410607078580494947569605565) * 10 ^ 70 +
        7507883026161742910298483238958480606228257823478533078749987549740891) * 10 ^ 70 +
        4919300808531069424703293373630700574331090470322523620636083039084811) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (392 - x)) = _
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
    rw [show 251 = 27 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (393 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_393 :
    recurrence4Scalar2Second.coeff 393 =
      ((((124789584315940123608407122840916853288290024927182712802003 * 10 ^ 70 +
        5697942637806439050079264507655429508787845759742569939158027932105556) * 10 ^ 70 +
        1580864610251390953523302031124613746063205649078220020766074161765292) * 10 ^ 70 +
        6313343480718794449919821729456324708263357358799414001343673393521153) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (393 - x)) = _
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
    rw [show 251 = 26 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (394 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_394 :
    recurrence4Scalar2Second.coeff 394 =
      -((((45502480244245857745027568896497683739972147771630333974629 * 10 ^ 70 +
        3855270544440012843807723930598012966652192850089209798346861119574801) * 10 ^ 70 +
        9896772545774614299895604629663612245736330059708050391071412580569321) * 10 ^ 70 +
        4343995145841309192182254495768399928846784139661496875080332694518699) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (394 - x)) = _
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
    rw [show 251 = 25 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (395 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_395 :
    recurrence4Scalar2Second.coeff 395 =
      ((((16057700276292197291541877022451046421008577190163671545108 * 10 ^ 70 +
        5427660529936096198878402080754028245876617546568062671925276219475783) * 10 ^ 70 +
        3073414261087834734215672227414147335576882883302184820186413208658136) * 10 ^ 70 +
        4868703382567130219928928075894698390428396789186170564874523000695464) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (395 - x)) = _
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
    rw [show 251 = 24 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (396 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_396 :
    recurrence4Scalar2Second.coeff 396 =
      -((((5471953280461656606858347923145781899885419663597098545742 * 10 ^ 70 +
        1658911142727291076871353771090798200459117265365596659977867800020472) * 10 ^ 70 +
        8772149109848810972338285006848496752893846409563058869572288816495635) * 10 ^ 70 +
        8984872907714986423740810543066447743591686210988131630738068595854932) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (396 - x)) = _
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
    rw [show 251 = 23 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (397 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_397 :
    recurrence4Scalar2Second.coeff 397 =
      ((((1796231564784907584397291980212698407350598054874495788034 * 10 ^ 70 +
        2009884713079349869894837319489302741602906454084850365514478607119418) * 10 ^ 70 +
        5342756100408183513960427422603319950537769899055149146582894572261022) * 10 ^ 70 +
        5880076676524730873879231324849017364316926669066778492661448302494812) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (397 - x)) = _
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
    rw [show 251 = 22 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (398 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_398 :
    recurrence4Scalar2Second.coeff 398 =
      -((((566258740503927008522145264296071471469400429048849059017 * 10 ^ 70 +
        0262460792453394030443992560473897102822009631155260665788051687864684) * 10 ^ 70 +
        4279266681234394106416343334965939112346033108581527644664893354654756) * 10 ^ 70 +
        6351450994793218087509182878396578605130564349834908265109015141825201) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (398 - x)) = _
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
    rw [show 251 = 21 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (399 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_399 :
    recurrence4Scalar2Second.coeff 399 =
      ((((170700718270930801310297655826129814466328054265418198078 * 10 ^ 70 +
        8478194116694847764279454116068001758738471405937378009577761809865048) * 10 ^ 70 +
        9853918344482398274138348667674733507018442114867038906188508045919486) * 10 ^ 70 +
        9408151298233333132081674964966986386119559313366320030928164269411031) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (399 - x)) = _
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
    rw [show 251 = 20 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (400 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_400 :
    recurrence4Scalar2Second.coeff 400 =
      -((((48888765859135761166528292151799161309904492994406055573 * 10 ^ 70 +
        6038785012898554123163005161300756983990059252287021111881669174324483) * 10 ^ 70 +
        2517255624885915478321348860994224451903204266234284782982677254182203) * 10 ^ 70 +
        4287895578256740317186135204767820429826254546125428549410094252431474) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (400 - x)) = _
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
    rw [show 251 = 19 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (401 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_401 :
    recurrence4Scalar2Second.coeff 401 =
      ((((13163032862390767396915065099277408140049435396674650847 * 10 ^ 70 +
        7871397936426544689660273854471917895351976123942526349001414730385793) * 10 ^ 70 +
        1785953569357239970204423176828919771606990227588750062811612889113509) * 10 ^ 70 +
        6602426839046426757764890841811797987424233185622630944599275715597489) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (401 - x)) = _
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
    rw [show 251 = 18 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (402 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_402 :
    recurrence4Scalar2Second.coeff 402 =
      -((((3268909180199370309448447736278209201053722401089312978 * 10 ^ 70 +
        8153169838007512737265651676564625430651335325088434498102691163769448) * 10 ^ 70 +
        8090144957293415209359864804999100730374670863962576427674039755066344) * 10 ^ 70 +
        7445435588603163790565440522900314334103264350178103609805015449324147) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (402 - x)) = _
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
    rw [show 251 = 17 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (403 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_403 :
    recurrence4Scalar2Second.coeff 403 =
      ((((719055465704182842339535705182634799371746315347711248 * 10 ^ 70 +
        5207919243463583672807232658257506817790769997266195778239108185701133) * 10 ^ 70 +
        1591448497811589258447906284384754487778302642929735100022727164143486) * 10 ^ 70 +
        5136012427345539003491309070743139656272116985740375891692279312625427) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (403 - x)) = _
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
    rw [show 251 = 16 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (404 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_404 :
    recurrence4Scalar2Second.coeff 404 =
      -((((124856346818661645365782757548679405579187998543553925 * 10 ^ 70 +
        0661234857650624070936995475429463658617702899530775298249960595238977) * 10 ^ 70 +
        7445327542376982989565772448264249158981377811696740790941625791310592) * 10 ^ 70 +
        0221026794162329924099801853854692474262673112446306219641339283958519) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (404 - x)) = _
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
    rw [show 251 = 15 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (405 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_405 :
    recurrence4Scalar2Second.coeff 405 =
      ((((8129778258307879150095104720380887702641273600186563 * 10 ^ 70 +
        8748793610636847434647677790046755384864112094902948866478879220645987) * 10 ^ 70 +
        6112418209960702804307449966603262128686372178498807334167029200411806) * 10 ^ 70 +
        9887141778466612161947334146771702714650261970372000434679013945837525) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (405 - x)) = _
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
    rw [show 251 = 14 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (406 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_406 :
    recurrence4Scalar2Second.coeff 406 =
      ((((6561259004932580782875698199898909209660093249025644 * 10 ^ 70 +
        9129049956221149632294684580149361379795683852269660228211438205980048) * 10 ^ 70 +
        0001060170465455114145654263313789716025326266812359634903445954560720) * 10 ^ 70 +
        9615667114951695441391380380547029364293068831086401536333064844328976) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (406 - x)) = _
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
    rw [show 251 = 13 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (407 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_407 :
    recurrence4Scalar2Second.coeff 407 =
      -((((4666868121591491902847962306381001276908945705581348 * 10 ^ 70 +
        1610249783615775625007629753340521390209428477985912520648876200382712) * 10 ^ 70 +
        5469481243930969682095790961692849348732251655292599947426692920359315) * 10 ^ 70 +
        2375589680749173513592938668987693606836110260920708537473446903141492) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (407 - x)) = _
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
    rw [show 251 = 12 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (408 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_408 :
    recurrence4Scalar2Second.coeff 408 =
      ((((2220174126608253740336951233112361622268948740022593 * 10 ^ 70 +
        0147810760974591543486675247010902611273491117343910995379573419864475) * 10 ^ 70 +
        2202169286459303905509919756402074400206537908856839968235970417094729) * 10 ^ 70 +
        9514518720686663453867870654367692327075371813163280046905816401422188) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (408 - x)) = _
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
    rw [show 251 = 11 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (409 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_409 :
    recurrence4Scalar2Second.coeff 409 =
      -((((929332780992938557503505302941930032352205747950721 * 10 ^ 70 +
        3218345553986088459950372655824070392780542518127017580004712569130827) * 10 ^ 70 +
        7715758572055304268735935984547165696507227095919938829212807545862421) * 10 ^ 70 +
        1626955555836882612247028411521948889452253268815761450386119718389140) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (409 - x)) = _
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
    rw [show 251 = 10 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (410 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_410 :
    recurrence4Scalar2Second.coeff 410 =
      ((((370365876769692548981651463164310968908972005911160 * 10 ^ 70 +
        6354928367993281769337725035894489501339760178184578289502870413525852) * 10 ^ 70 +
        1551583102736564564470770272745768593282737275379532482485057471320739) * 10 ^ 70 +
        9660260368606630487725899724288126640933318328305894029964113764201438) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (410 - x)) = _
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
    rw [show 251 = 9 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (411 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_411 :
    recurrence4Scalar2Second.coeff 411 =
      -((((145311054170239149027891726908556541341005967400859 * 10 ^ 70 +
        1352049747843169736594063462968998223450767973859754387316186219269120) * 10 ^ 70 +
        8227888447745078768667002411231325115580682986406555767146465984024450) * 10 ^ 70 +
        7903361431257199451176023776585341814919346214359534048017036327534836) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (411 - x)) = _
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
    rw [show 251 = 8 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (412 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_412 :
    recurrence4Scalar2Second.coeff 412 =
      ((((56856042375206860706679989139621601293906809712379 * 10 ^ 70 +
        5229221945985715078284437865851275480159600663267944305680641288383567) * 10 ^ 70 +
        6462949264911761812501150918457245807731506655341184524727771979689120) * 10 ^ 70 +
        0635108648961299329419378452604571209421228062824178194867302043383025) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (412 - x)) = _
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
    rw [show 251 = 7 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (413 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_413 :
    recurrence4Scalar2Second.coeff 413 =
      -((((22209618914376793208836019575375385413408346485333 * 10 ^ 70 +
        8604487469357408421666765569496330598533933462824479184994171902606272) * 10 ^ 70 +
        3211670420571946666424677508356410912302385489328432950198286704406351) * 10 ^ 70 +
        3178581785441805062352701161918420525850264740027699833734326622474478) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (413 - x)) = _
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
    rw [show 251 = 6 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (414 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_414 :
    recurrence4Scalar2Second.coeff 414 =
      ((((8619446454678887775823500398157473542877776099591 * 10 ^ 70 +
        7214438159500174292838751631027394390632152290209088329552750881102970) * 10 ^ 70 +
        3705370236662208333124861633473707242684899922062205828363443972623225) * 10 ^ 70 +
        5614377569306273109972075165854661620043972755976626757181840793425998) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (414 - x)) = _
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
    rw [show 251 = 5 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (415 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_415 :
    recurrence4Scalar2Second.coeff 415 =
      -((((3301543434640573505675844522084103870286492356780 * 10 ^ 70 +
        4459018483980971177245553445600578088846867901798096980222951216825457) * 10 ^ 70 +
        2171126197793582741836040592415072699129357962301404242619262954328988) * 10 ^ 70 +
        3945340517929156342048318178924694572274541644945140611451889306637177) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (415 - x)) = _
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
    rw [show 251 = 4 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (416 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_416 :
    recurrence4Scalar2Second.coeff 416 =
      ((((1240578126805437064424351326208451399821659936620 * 10 ^ 70 +
        1033384288931727758022378088801959482340192801383528718542723839525458) * 10 ^ 70 +
        3285887515881002474632212206506839585822706265422990129293807371460814) * 10 ^ 70 +
        2302035747058403828512732265307481122388779246988220095863199605603987) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (416 - x)) = _
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
    rw [show 251 = 3 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (417 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_417 :
    recurrence4Scalar2Second.coeff 417 =
      -((((455143814675140925933239538377787542705826583104 * 10 ^ 70 +
        8038041600995563877495741806231492100711211895143790762017709901714195) * 10 ^ 70 +
        3500680904116024683152530782065958019666662265138371271708556334607299) * 10 ^ 70 +
        7247721678158179135664040833432621605779080486344695801946952005726632) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (417 - x)) = _
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
    rw [show 251 = 2 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (418 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_418 :
    recurrence4Scalar2Second.coeff 418 =
      ((((162471396545109746935142503547380459981379085151 * 10 ^ 70 +
        5997715922622047523089994942788519728970039108175948255592851346848776) * 10 ^ 70 +
        5992998731476777093629345387349726707986386443367901737647505648096972) * 10 ^ 70 +
        6513175945576661735518983940714294892040530201786495330865987490454387) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (418 - x)) = _
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
    rw [show 251 = 1 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (419 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_419 :
    recurrence4Scalar2Second.coeff 419 =
      -((((56280818170036187217858892016567261798756744460 * 10 ^ 70 +
        7667744237110549124544061684517563202666830055205075889994495899172431) * 10 ^ 70 +
        0086859118470066155419956599569651924880140854564246859122383509274762) * 10 ^ 70 +
        7239163850951677255242184319132808671362903908744129639766665918871812) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (419 - x)) = _
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
  rw [recurrence4Scalar2Second_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (420 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_420 :
    recurrence4Scalar2Second.coeff 420 =
      ((((18876935497679310724731119770700880931365329124 * 10 ^ 70 +
        7887430276439699380322411409322523902814487292565587103201905690583536) * 10 ^ 70 +
        1927468541975286650285764530794957295936696940491245469837435400825607) * 10 ^ 70 +
        7531473844249246261989811212282803641038586039289795509718502750615546) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (420 - x)) = _
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
    rw [show 283 = 31 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (421 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_421 :
    recurrence4Scalar2Second.coeff 421 =
      -((((6117131589704635086033437765483973653372659745 * 10 ^ 70 +
        7068224279228767423738402397312305150871726806891009520519582269154705) * 10 ^ 70 +
        9069893750548638619065585865041848449147472965803348358282997032435810) * 10 ^ 70 +
        2107539882345846653277762019458547476303840105346750893259981600320161) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (421 - x)) = _
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
    rw [show 283 = 30 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (422 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_422 :
    recurrence4Scalar2Second.coeff 422 =
      ((((1910569662052504964423833655250720841004374519 * 10 ^ 70 +
        7868690615976452243096116413979395649990804780484308407746332228140361) * 10 ^ 70 +
        0505629164153602343692896413934505590717586164280859253763791435890994) * 10 ^ 70 +
        8346539611397631428645876802738483071004675742627696435149320911110554) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (422 - x)) = _
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
    rw [show 283 = 29 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (423 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_423 :
    recurrence4Scalar2Second.coeff 423 =
      -((((573457853122001555860307905871762517119711474 * 10 ^ 70 +
        6750835447901986611150502030724415280367604874097706219799321635888916) * 10 ^ 70 +
        3077656171321884072321322209264707146862243016350710548984754187101307) * 10 ^ 70 +
        7243896650941138861251903125517178112448782087003131552927392233432221) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (423 - x)) = _
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
    rw [show 283 = 28 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (424 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_424 :
    recurrence4Scalar2Second.coeff 424 =
      ((((164780662462622325359469039247215453957851980 * 10 ^ 70 +
        6993993168091601198745062779730758675688019771000898123282393615767152) * 10 ^ 70 +
        0119010887467248644771306923763239303740723273759982486102277178930466) * 10 ^ 70 +
        8234818638546556832266596726315512813124737379839910846189868459780473) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (424 - x)) = _
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
    rw [show 283 = 27 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (425 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_425 :
    recurrence4Scalar2Second.coeff 425 =
      -((((45091874752896831696565080032115461851343095 * 10 ^ 70 +
        5506243649281618125254095443082391177486819458253197829926171836930714) * 10 ^ 70 +
        6055786000999109668603244157696424678342802275822942972069535453182003) * 10 ^ 70 +
        1370860580581611059408415071658233768921717605151288837349584352169271) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (425 - x)) = _
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
    rw [show 283 = 26 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (426 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_426 :
    recurrence4Scalar2Second.coeff 426 =
      ((((11661151472686361324143124985016066097628148 * 10 ^ 70 +
        8517015912903218637717649197978162574483559538336068904641412016044751) * 10 ^ 70 +
        2517583747271856718175680986767939352192931650217099088090755227197048) * 10 ^ 70 +
        5879067342013708205768061950002066363426663517931928068942321692847623) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (426 - x)) = _
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
    rw [show 283 = 25 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (427 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_427 :
    recurrence4Scalar2Second.coeff 427 =
      -((((2815398486048892420997387102843053534993141 * 10 ^ 70 +
        5864627804467813194235553135639605987789837900777301201683167722918938) * 10 ^ 70 +
        3964481960492609983508624280440562575043175497319595426368431378754361) * 10 ^ 70 +
        8924850015202088406960747784872960110533061482892630196951683867116354) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (427 - x)) = _
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
    rw [show 283 = 24 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (428 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_428 :
    recurrence4Scalar2Second.coeff 428 =
      ((((620991241758961415419300612100046813607585 * 10 ^ 70 +
        2923000125394812791595758966646478887559169374709211049650203569308821) * 10 ^ 70 +
        6356825140521699829236566370890511421134029433316111344540817824844737) * 10 ^ 70 +
        8906754151266977976583762078366671437779251452453538307608658916347412) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (428 - x)) = _
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
    rw [show 283 = 23 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (429 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_429 :
    recurrence4Scalar2Second.coeff 429 =
      -((((119546659637121521459535275379549356629284 * 10 ^ 70 +
        8340510300830570786608678905964087448818573174849157189497948855799985) * 10 ^ 70 +
        9991162850187627185060573850778356045161814905600693807327071270086670) * 10 ^ 70 +
        8773645478811146708720774200053301049842045978034491041726774427442553) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (429 - x)) = _
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
    rw [show 283 = 22 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (430 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_430 :
    recurrence4Scalar2Second.coeff 430 =
      ((((17613991774016421564791489360659172105406 * 10 ^ 70 +
        7592006031937224459448878574567959180262074590748371667547800967450513) * 10 ^ 70 +
        7368311948765229555536726401247456072048369284796315589195465243331638) * 10 ^ 70 +
        4506916667665925458485047556731623548367768171906697996926024296868392) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (430 - x)) = _
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
    rw [show 283 = 21 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (431 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_431 :
    recurrence4Scalar2Second.coeff 431 =
      -((((736659179960596210971055273221154910995 * 10 ^ 70 +
        8405457577191949975785200257649636748762255149893480971501491764717193) * 10 ^ 70 +
        4810461010592422297318075028453440455545804455696975872572975140030386) * 10 ^ 70 +
        7625448831141801475870016533059632336443028386561242857432045554508429) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (431 - x)) = _
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
    rw [show 283 = 20 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (432 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_432 :
    recurrence4Scalar2Second.coeff 432 =
      -((((793752699972652138849312554735857148663 * 10 ^ 70 +
        8239191679094930629357594476005628229952986025457661181013222126494417) * 10 ^ 70 +
        0917723449936951136133682229748840289547650213872354809976400157688377) * 10 ^ 70 +
        9497113500757767488991682639382460180778397244678174238933030348302498) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (432 - x)) = _
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
    rw [show 283 = 19 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (433 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_433 :
    recurrence4Scalar2Second.coeff 433 =
      ((((432069074281742271879655632309666337512 * 10 ^ 70 +
        9897868961801241256971758150669827749437701017363818131451203599832081) * 10 ^ 70 +
        0475195361686466203480004535365452737440599942718831278413338656186008) * 10 ^ 70 +
        7014017428966335463791093958635784663630480086430878469923997121109464) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (433 - x)) = _
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
    rw [show 283 = 18 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (434 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_434 :
    recurrence4Scalar2Second.coeff 434 =
      -((((157269419995314688245163554790850804194 * 10 ^ 70 +
        5978861148734566780107243987527739343945312174208525787277896222806190) * 10 ^ 70 +
        4255725849057223555165712509291840345350770379832335331720593740917857) * 10 ^ 70 +
        0437407965179544356453187287950608461124285418305705847337449531422468) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (434 - x)) = _
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
    rw [show 283 = 17 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (435 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_435 :
    recurrence4Scalar2Second.coeff 435 =
      ((((48045114306676685971388444993852890838 * 10 ^ 70 +
        5348943463908666922394316160663105726757399120329342904299199232768617) * 10 ^ 70 +
        3373915204981488142031699533160285835324605257797959260720441013646039) * 10 ^ 70 +
        7622626588515093892830201110291475586981152259721980035486567937187234) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (435 - x)) = _
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
    rw [show 283 = 16 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (436 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_436 :
    recurrence4Scalar2Second.coeff 436 =
      -((((13110163102480108470102194290624099876 * 10 ^ 70 +
        6530334581133266280905265841499385945872384248132658688966869891036156) * 10 ^ 70 +
        4883353507748966475121865969792400453845682564329831035589756131770337) * 10 ^ 70 +
        3273550048760452641164607862057403184267956399443009915115562264566203) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (436 - x)) = _
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
    rw [show 283 = 15 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (437 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_437 :
    recurrence4Scalar2Second.coeff 437 =
      ((((3276595342382490564917959221431736350 * 10 ^ 70 +
        0270922953434187614560274914769352693680711186087642323016725636492882) * 10 ^ 70 +
        3348473445090886274208026457243220302989497479114889073057187881159806) * 10 ^ 70 +
        6787994257826034028769677426123830086825551779425382295259167852059979) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (437 - x)) = _
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
    rw [show 283 = 14 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (438 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_438 :
    recurrence4Scalar2Second.coeff 438 =
      -((((758805710912035408401982118382466577 * 10 ^ 70 +
        0742871833230143851908015715567838260879614249532280391842108825343196) * 10 ^ 70 +
        5138046388921479206264536764111420361253138173256998420857356855536065) * 10 ^ 70 +
        7390794053573933225610069627933086211875607385205608274723438242754443) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (438 - x)) = _
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
    rw [show 283 = 13 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (439 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_439 :
    recurrence4Scalar2Second.coeff 439 =
      ((((163673537480066441041870062860359513 * 10 ^ 70 +
        9316582351691554244125156356845915073933303710301886718946039918564984) * 10 ^ 70 +
        1254446479811114139813892099460676909142680573242091056060377843290819) * 10 ^ 70 +
        6159858072120732924297296161690097185634607710654018119116809305855942) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (439 - x)) = _
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
    rw [show 283 = 12 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (440 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_440 :
    recurrence4Scalar2Second.coeff 440 =
      -((((32926429242139503608579280162845895 * 10 ^ 70 +
        6185737585976596141269239239420621505288516517831243606420065727281216) * 10 ^ 70 +
        7176761645424310299215159786645174576234873270616821840107145854151331) * 10 ^ 70 +
        2050869138564947039278922817822119249011296903343753610632155254199234) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (440 - x)) = _
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
    rw [show 283 = 11 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (441 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_441 :
    recurrence4Scalar2Second.coeff 441 =
      ((((6167667844965404942067959332992127 * 10 ^ 70 +
        1036629597624106339108317393936549289880894172085472520735036252567079) * 10 ^ 70 +
        6819253012154449897885079785785710732154409311123918809485742594116738) * 10 ^ 70 +
        5960989432368620863904942291725923591708549698453699981843385737995593) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (441 - x)) = _
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
    rw [show 283 = 10 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (442 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_442 :
    recurrence4Scalar2Second.coeff 442 =
      -((((1070726584205785044738918285234268 * 10 ^ 70 +
        9566740882179156074471474235253017559826996635593151330336840512824853) * 10 ^ 70 +
        7359870918888888086666103797443017540700860311832927009167908444467089) * 10 ^ 70 +
        3535476901498395914280213961336283607734260839465925647853767138963367) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (442 - x)) = _
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
    rw [show 283 = 9 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (443 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_443 :
    recurrence4Scalar2Second.coeff 443 =
      ((((170765371026368260757174483901687 * 10 ^ 70 +
        6277590127268297728130993880076773023211580875544172951364938627592862) * 10 ^ 70 +
        7727643971677004602595715885765760026745860050054020019097796517072066) * 10 ^ 70 +
        9783078990677835504537998483905427077525162132568124243347491430795401) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (443 - x)) = _
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
    rw [show 283 = 8 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (444 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_444 :
    recurrence4Scalar2Second.coeff 444 =
      -((((24626309954683550120593863822881 * 10 ^ 70 +
        3519161510661082259691506989512776790661498390622022033555395958829216) * 10 ^ 70 +
        5728112861651240801987696108203551761730283918102900628207066025989403) * 10 ^ 70 +
        3215642569582519772720162272539774870281985019878501523958585155137874) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (444 - x)) = _
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
    rw [show 283 = 7 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (445 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_445 :
    recurrence4Scalar2Second.coeff 445 =
      ((((3113368322824740457758185963490 * 10 ^ 70 +
        7388962727859133498085588895518725765539506235991213064196750039691347) * 10 ^ 70 +
        4461770126352647277804038352329210200997627978860851883422018338283711) * 10 ^ 70 +
        8089808359004994773649919904509265655770730414880474553536184136405479) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (445 - x)) = _
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
    rw [show 283 = 6 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (446 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_446 :
    recurrence4Scalar2Second.coeff 446 =
      -((((320558172272480639370358133474 * 10 ^ 70 +
        4327671519813289745625890646010792027478088314734710295707847329794169) * 10 ^ 70 +
        5351960922296548739866092506097838383464101882707374187824816740968145) * 10 ^ 70 +
        0152793404221969409614841836821402476311274723700008624428465352411524) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (446 - x)) = _
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
    rw [show 283 = 5 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (447 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_447 :
    recurrence4Scalar2Second.coeff 447 =
      ((((20351041710268114659293878274 * 10 ^ 70 +
        6167025714354071385230514546713990454448702456671928919251355264664556) * 10 ^ 70 +
        2457995219704911745638239012182424574896275621670866941426704117845449) * 10 ^ 70 +
        7390852130316816938908301285537536464620292834771840364606052619876713) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (447 - x)) = _
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
    rw [show 283 = 4 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (448 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_448 :
    recurrence4Scalar2Second.coeff 448 =
      ((((1231373220293710108350461824 * 10 ^ 70 +
        6953375222458084894599165201827464434666928992370991564119849869301902) * 10 ^ 70 +
        1776061720377478655734952189959451485389205297104196349091512825871053) * 10 ^ 70 +
        6272458610600658096280846591692817603796560660371330746758227868058382) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (448 - x)) = _
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
    rw [show 283 = 3 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (449 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_449 :
    recurrence4Scalar2Second.coeff 449 =
      -((((722419293867099086142045695 * 10 ^ 70 +
        8374216141205462041942905541548376359458796901003096123674880344532703) * 10 ^ 70 +
        2710306294568467991784753848438812775005807481835900080436968850448234) * 10 ^ 70 +
        7933942703113751334239989292108242213021908820440826333141643150409738) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (449 - x)) = _
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
    rw [show 283 = 2 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (450 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_450 :
    recurrence4Scalar2Second.coeff 450 =
      ((((158344584194332632583826392 * 10 ^ 70 +
        1080974622447210442725747545438895670828225402383643312796191054741149) * 10 ^ 70 +
        7411609808754016936128479160569148504424935151234412907830555275253930) * 10 ^ 70 +
        1379727851671197507969849406774010381262122845195896004265143456733837) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (450 - x)) = _
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
    rw [show 283 = 1 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (451 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_451 :
    recurrence4Scalar2Second.coeff 451 =
      -((((25640563282457159778894147 * 10 ^ 70 +
        0496917180741013504966138507149465907042113571245176527109254860210890) * 10 ^ 70 +
        6983132385972271963559877590590390305944425165894144578490138104170872) * 10 ^ 70 +
        3280683460401443061043824140387261486784592961789425365409933773636404) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (451 - x)) = _
  rw [show 452 = 105 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (452 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_452 :
    recurrence4Scalar2Second.coeff 452 =
      ((((3364722209821316273286110 * 10 ^ 70 +
        4330963123210683727967865135670085466796713206053429493996783832805983) * 10 ^ 70 +
        7476341031080153701591523756042070719298451455474830789336213588198240) * 10 ^ 70 +
        2486525986073599675169271485528190972379126048073788315077772522544112) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (452 - x)) = _
  rw [show 453 = 106 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 31 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (453 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_453 :
    recurrence4Scalar2Second.coeff 453 =
      -((((357553346544356884115110 * 10 ^ 70 +
        0569782724342988498511659868584663626738237929341876083085961478445186) * 10 ^ 70 +
        5469942399958396352861445341949827193879340334798743336788513515826703) * 10 ^ 70 +
        1467262094247317283984540766607817764635150907906320708208229473024822) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (453 - x)) = _
  rw [show 454 = 107 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 30 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (454 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_454 :
    recurrence4Scalar2Second.coeff 454 =
      ((((28174834682723670314212 * 10 ^ 70 +
        2173604962961571196138477626066375529722202570872381786058122522668259) * 10 ^ 70 +
        4570746738045395607663719871252518234121453556638619944705263494448155) * 10 ^ 70 +
        4974352798130200755079397219934460416600231441853142429040920762482821) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (454 - x)) = _
  rw [show 455 = 108 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 29 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (455 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_455 :
    recurrence4Scalar2Second.coeff 455 =
      -((((946543981300131397011 * 10 ^ 70 +
        9067941380840556190997101540695883788124970042305433144532052604640244) * 10 ^ 70 +
        0212867706225624624892354353100520912122195254790598660126555787276617) * 10 ^ 70 +
        9777409346777126390170412926239423981871346765290104041030627417415288) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (455 - x)) = _
  rw [show 456 = 109 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 28 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (456 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_456 :
    recurrence4Scalar2Second.coeff 456 =
      -((((177460763291580803331 * 10 ^ 70 +
        1496279415093435651136427610052562733249638745523093523167418387124075) * 10 ^ 70 +
        5842121920885821540353563535419866098749645416198220602077763671090941) * 10 ^ 70 +
        7432552362903352231921887980902060081087711221121870466085661389613736) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (456 - x)) = _
  rw [show 457 = 110 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 27 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (457 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_457 :
    recurrence4Scalar2Second.coeff 457 =
      ((((46605038430643270470 * 10 ^ 70 +
        8964377868188825378910501538984751405347150743366543721776414979127204) * 10 ^ 70 +
        8469698631721987177392724037382592405828230088933327310849170709825706) * 10 ^ 70 +
        3803768158428221532324821110701662380307429580206523036559632374759715) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (457 - x)) = _
  rw [show 458 = 111 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 26 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (458 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_458 :
    recurrence4Scalar2Second.coeff 458 =
      -((((6814253508931233512 * 10 ^ 70 +
        9753022695494987312008970056166540556997835694774276165715965049873753) * 10 ^ 70 +
        2393094604091600598835141624505645140251257539986000040342921240248193) * 10 ^ 70 +
        7351347006457917285392717491449090226890401585432808819703029551635854) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (458 - x)) = _
  rw [show 459 = 112 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 25 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (459 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_459 :
    recurrence4Scalar2Second.coeff 459 =
      ((((750916194576151326 * 10 ^ 70 +
        2578021741901099060724799702760890282910172536770855195498108231271170) * 10 ^ 70 +
        7571125752570288099295182436364868579181207530773724833922711010495329) * 10 ^ 70 +
        9910892885686566393144505676845198500073303833519179999284176362717686) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (459 - x)) = _
  rw [show 460 = 113 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 24 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (460 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_460 :
    recurrence4Scalar2Second.coeff 460 =
      -((((65491593050481491 * 10 ^ 70 +
        2810937014790676811901162789324262122405699064526892093698105289704525) * 10 ^ 70 +
        4595197946061864495488428603085693164022674066219188875857082013611657) * 10 ^ 70 +
        9998097201111606807256393771359230125217237915662507523801330217238025) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (460 - x)) = _
  rw [show 461 = 114 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 23 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (461 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_461 :
    recurrence4Scalar2Second.coeff 461 =
      ((((4384877209199917 * 10 ^ 70 +
        0706823791254111554212820225386945986671850484075800348179670607026515) * 10 ^ 70 +
        6727186451779464982352394786253764777034005978723851887224338437894851) * 10 ^ 70 +
        0402824175672042540740991837687569457397506995622219630371131706030938) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (461 - x)) = _
  rw [show 462 = 115 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 22 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (462 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_462 :
    recurrence4Scalar2Second.coeff 462 =
      -((((188905504421351 * 10 ^ 70 +
        3890375566070051850203106703898441920293321730263836599590363495957999) * 10 ^ 70 +
        0248857924878348215047542751024925731602372601401603461610387389228947) * 10 ^ 70 +
        3027053123824589850143969937458046482622188288346188932469043347033210) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (462 - x)) = _
  rw [show 463 = 116 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 21 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (463 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_463 :
    recurrence4Scalar2Second.coeff 463 =
      -((((861565023595 * 10 ^ 70 +
        8002381770865612867751912785458309628823531636377131441081825481894875) * 10 ^ 70 +
        0395399113115083899766868213586234962039759074327620221946902806355185) * 10 ^ 70 +
        3868083961003376809168881151596082759993665126649121890064017341381303) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (463 - x)) = _
  rw [show 464 = 117 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 20 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (464 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_464 :
    recurrence4Scalar2Second.coeff 464 =
      ((((1097668643275 * 10 ^ 70 +
        0270754034465384189149280384907785116539851222547014574446402900527547) * 10 ^ 70 +
        9563315350454019322644966656720321481458979248499176930716606077334548) * 10 ^ 70 +
        4081064237348495030776405017009218299103957397938741664495061104187232) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (464 - x)) = _
  rw [show 465 = 118 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 19 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (465 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_465 :
    recurrence4Scalar2Second.coeff 465 =
      -((((121873405845 * 10 ^ 70 +
        8065431995941171561839609868749743877258379260011596103373432760823465) * 10 ^ 70 +
        2513995994187173508099403510589417325666590007852983786982181420455796) * 10 ^ 70 +
        2273453051486015124990875349485456279036788719221802453038740010560419) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (465 - x)) = _
  rw [show 466 = 119 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 18 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (466 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_466 :
    recurrence4Scalar2Second.coeff 466 =
      ((((8474181497 * 10 ^ 70 +
        8869728089011712456696244047016248383369394127681200841454552553807388) * 10 ^ 70 +
        1262592589485919984884993736029142234983348787184805687761871638054045) * 10 ^ 70 +
        9003281116712982170381195996590143209696722699099575294073078834451825) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (466 - x)) = _
  rw [show 467 = 120 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 17 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (467 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_467 :
    recurrence4Scalar2Second.coeff 467 =
      -((((399545129 * 10 ^ 70 +
        9504692535101430955752064306395723914266508159385997802554803593047224) * 10 ^ 70 +
        3534836404437718027945281647981532511278294400877816971139136402872886) * 10 ^ 70 +
        6630764210743681922106165457580547437194375534766202142436734620257293) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (467 - x)) = _
  rw [show 468 = 121 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 16 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (468 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_468 :
    recurrence4Scalar2Second.coeff 468 =
      ((((10389416 * 10 ^ 70 +
        4635353114819272205815316459016013593838781044067990091577824133292941) * 10 ^ 70 +
        2698569841795781497673974164444039544759189278770954253386808183398980) * 10 ^ 70 +
        3798289102595034668543593833110865527348158902780712898920757706128619) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (468 - x)) = _
  rw [show 469 = 122 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 15 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (469 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_469 :
    recurrence4Scalar2Second.coeff 469 =
      ((((140009 * 10 ^ 70 +
        7032947988699762058816540155365527803993315518356672275390632801859134) * 10 ^ 70 +
        1295067815795475273731427535012249038264964252757424703064737643803808) * 10 ^ 70 +
        9642370777018498830769035152307928594883727222494614659939423759050210) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (469 - x)) = _
  rw [show 470 = 123 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 14 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (470 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_470 :
    recurrence4Scalar2Second.coeff 470 =
      -((((28978 * 10 ^ 70 +
        3486407830252397987186659322545360277569953683807865702382609463428084) * 10 ^ 70 +
        2518940851101389123563650334967114606965671172983403611057547947332501) * 10 ^ 70 +
        8698990489163933513750293203849474078471751163406522066137668847546501) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (470 - x)) = _
  rw [show 471 = 124 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 13 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (471 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_471 :
    recurrence4Scalar2Second.coeff 471 =
      ((((1435 * 10 ^ 70 +
        7229015899861859339975080808609975467626571968055519745194681616489090) * 10 ^ 70 +
        9161557727432069330289080342775996277365729982733082256148012306213970) * 10 ^ 70 +
        2263562133186625465635177253053244585024878684287508432951663164905935) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (471 - x)) = _
  rw [show 472 = 125 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 12 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (472 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_472 :
    recurrence4Scalar2Second.coeff 472 =
      -((((33 * 10 ^ 70 +
        4581825536398311734225102371115204865676555440471642296222996298857660) * 10 ^ 70 +
        8002344986894532504925169271033325761700621207075688192312203216172428) * 10 ^ 70 +
        9735658900738101339121963926030588036745123009677221686164809671118589) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (472 - x)) = _
  rw [show 473 = 126 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 11 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (473 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_473 :
    recurrence4Scalar2Second.coeff 473 =
      -(((707269874667918314929359153216612114842549322864250536246095950147426 * 10 ^ 70 +
        8390052763287091523763189790449394884221446128226522636180540189913061) * 10 ^ 70 +
        5228620849385141686452004766909943305134114736354818008281173123757601) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (473 - x)) = _
  rw [show 474 = 127 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 10 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (474 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_474 :
    recurrence4Scalar2Second.coeff 474 =
      (((279483511438188234011092392587782642208848150848610612967504069079348 * 10 ^ 70 +
        3738811189360166102021324422017249803308969897644356057952912793373038) * 10 ^ 70 +
        9631531468699636584846780053575916350628491885030303296332949169192746) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (474 - x)) = _
  rw [show 475 = 128 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 9 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (475 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_475 :
    recurrence4Scalar2Second.coeff 475 =
      -(((6524467799483159539077622667488868555687907236594317128635689121141 * 10 ^ 70 +
        5483771299672839060475131586868358127283634545679857291095129635585840) * 10 ^ 70 +
        7107563607285699795066043718048884380038668570301580600210445206168685) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (475 - x)) = _
  rw [show 476 = 129 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 8 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (476 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_476 :
    recurrence4Scalar2Second.coeff 476 =
      -(((6906969465145770726833472817119889100057938230220720696259641095 * 10 ^ 70 +
        4103067174230281525532830240356061729862080790094866434285801059178694) * 10 ^ 70 +
        7231048184296029641684716895964012667134643591455785873903889107884351) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (476 - x)) = _
  rw [show 477 = 130 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 7 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (477 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_477 :
    recurrence4Scalar2Second.coeff 477 =
      (((2252389839925873546658119627401411829980733992822650811639072483 * 10 ^ 70 +
        5056784605721216944443654881817385744546917324302105183884040453344242) * 10 ^ 70 +
        2330413640031571836972350950290095847833785504365919367629532579213984) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (477 - x)) = _
  rw [show 478 = 131 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 6 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Second_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4QuotientConstant_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Second_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder5Coefficient2.coeff (169 + x) *
        recurrence4QuotientConstant.coeff (478 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Second_coeff_478 :
    recurrence4Scalar2Second.coeff 478 =
      -(((13860060147810439006321603420081089109511427224673420852787953 * 10 ^ 70 +
        0271697780549604911151720562098714619770911648516332112572830469293300) * 10 ^ 70 +
        0373417726494990716463023312445026650629042244536420713094331152044038) : ℚ) := by
  unfold recurrence4Scalar2Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    remainder5Coefficient2.coeff x * recurrence4QuotientConstant.coeff (478 - x)) = _
  rw [show 479 = 132 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 315 = 5 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Second_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Second_coeff_478_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
