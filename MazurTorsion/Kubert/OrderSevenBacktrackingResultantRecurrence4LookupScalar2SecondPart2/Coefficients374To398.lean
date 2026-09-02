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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
