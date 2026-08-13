/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2SecondPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Second coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
