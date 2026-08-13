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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
