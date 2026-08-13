/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A2_coeff_100
  recurrence4A2_coeff_101
  recurrence4A2_coeff_102
  recurrence4A2_coeff_103
  recurrence4A2_coeff_104
  recurrence4A2_coeff_105
  recurrence4A2_coeff_106
  recurrence4A2_coeff_107
  recurrence4A2_coeff_108
  recurrence4A2_coeff_109
  recurrence4A2_coeff_110
  recurrence4A2_coeff_111
  recurrence4A2_coeff_112
  recurrence4A2_coeff_113
  recurrence4A2_coeff_114
  recurrence4A2_coeff_115
  recurrence4A2_coeff_116
  recurrence4A2_coeff_117
  recurrence4A2_coeff_118
  recurrence4A2_coeff_119
  recurrence4A2_coeff_120
  recurrence4A2_coeff_121
  recurrence4A2_coeff_122
  recurrence4A2_coeff_123
  recurrence4A2_coeff_124
  recurrence4A2_coeff_125
  recurrence4A2_coeff_126
  recurrence4A2_coeff_127
  recurrence4A2_coeff_128
  recurrence4A2_coeff_129
  recurrence4A2_coeff_130
  recurrence4A2_coeff_131
  recurrence4A2_coeff_132
  recurrence4A2_coeff_133
  recurrence4A2_coeff_134
  recurrence4A2_coeff_135
  recurrence4A2_coeff_136
  recurrence4A2_coeff_137
  recurrence4A2_coeff_138
  recurrence4A2_coeff_139
  recurrence4A2_coeff_140
  recurrence4A2_coeff_141
  recurrence4A2_coeff_142
  recurrence4A2_coeff_143
  recurrence4A2_coeff_144
  recurrence4A2_coeff_145
  recurrence4A2_coeff_146
  recurrence4A2_coeff_147
  recurrence4A2_coeff_148
  recurrence4A2_coeff_149
  recurrence4A2_coeff_150
  recurrence4A2_coeff_151
  recurrence4A2_coeff_152
  recurrence4A2_coeff_153
  recurrence4A2_coeff_154
  recurrence4A2_coeff_155
  recurrence4A2_coeff_156
  recurrence4A2_coeff_157
  recurrence4A2_coeff_158
  recurrence4A2_coeff_159
  recurrence4A2_coeff_160
  recurrence4A2_coeff_161
  recurrence4A2_coeff_162
  recurrence4A2_coeff_163

attribute [local simp]
  recurrence4A2_coeff_164
  recurrence4A2_coeff_165
  recurrence4A2_coeff_166
  recurrence4A2_coeff_167
  recurrence4A2_coeff_168
  recurrence4A2_coeff_169
  recurrence4A2_coeff_170
  recurrence4A2_coeff_171
  recurrence4A2_coeff_172
  recurrence4A2_coeff_173
  recurrence4A2_coeff_174
  recurrence4A2_coeff_175
  recurrence4A2_coeff_176
  recurrence4A2_coeff_177
  recurrence4A2_coeff_178
  recurrence4A2_coeff_179
  recurrence4A2_coeff_180
  recurrence4A2_coeff_181
  recurrence4A2_coeff_182
  recurrence4A2_coeff_183
  recurrence4A2_coeff_184
  recurrence4A2_coeff_185
  recurrence4A2_coeff_186
  recurrence4A2_coeff_30
  recurrence4A2_coeff_31
  recurrence4A2_coeff_32
  recurrence4A2_coeff_33
  recurrence4A2_coeff_34
  recurrence4A2_coeff_35
  recurrence4A2_coeff_36
  recurrence4A2_coeff_37
  recurrence4A2_coeff_38
  recurrence4A2_coeff_39
  recurrence4A2_coeff_40
  recurrence4A2_coeff_41
  recurrence4A2_coeff_42
  recurrence4A2_coeff_43
  recurrence4A2_coeff_44
  recurrence4A2_coeff_45
  recurrence4A2_coeff_46
  recurrence4A2_coeff_47
  recurrence4A2_coeff_48
  recurrence4A2_coeff_49
  recurrence4A2_coeff_50
  recurrence4A2_coeff_51
  recurrence4A2_coeff_52
  recurrence4A2_coeff_53
  recurrence4A2_coeff_54
  recurrence4A2_coeff_55
  recurrence4A2_coeff_56
  recurrence4A2_coeff_57
  recurrence4A2_coeff_58
  recurrence4A2_coeff_59
  recurrence4A2_coeff_60
  recurrence4A2_coeff_61
  recurrence4A2_coeff_62
  recurrence4A2_coeff_63
  recurrence4A2_coeff_64
  recurrence4A2_coeff_65
  recurrence4A2_coeff_66
  recurrence4A2_coeff_67
  recurrence4A2_coeff_68
  recurrence4A2_coeff_69
  recurrence4A2_coeff_70

attribute [local simp]
  recurrence4A2_coeff_71
  recurrence4A2_coeff_72
  recurrence4A2_coeff_73
  recurrence4A2_coeff_74
  recurrence4A2_coeff_75
  recurrence4A2_coeff_76
  recurrence4A2_coeff_77
  recurrence4A2_coeff_78
  recurrence4A2_coeff_79
  recurrence4A2_coeff_80
  recurrence4A2_coeff_81
  recurrence4A2_coeff_82
  recurrence4A2_coeff_83
  recurrence4A2_coeff_84
  recurrence4A2_coeff_85
  recurrence4A2_coeff_86
  recurrence4A2_coeff_87
  recurrence4A2_coeff_88
  recurrence4A2_coeff_89
  recurrence4A2_coeff_90
  recurrence4A2_coeff_91
  recurrence4A2_coeff_92
  recurrence4A2_coeff_93
  recurrence4A2_coeff_94
  recurrence4A2_coeff_95
  recurrence4A2_coeff_96
  recurrence4A2_coeff_97
  recurrence4A2_coeff_98
  recurrence4A2_coeff_99
  recurrence4LeadingSquare_coeff_172
  recurrence4LeadingSquare_coeff_173
  recurrence4LeadingSquare_coeff_174
  recurrence4LeadingSquare_coeff_175
  recurrence4LeadingSquare_coeff_176
  recurrence4LeadingSquare_coeff_177
  recurrence4LeadingSquare_coeff_178
  recurrence4LeadingSquare_coeff_179
  recurrence4LeadingSquare_coeff_180
  recurrence4LeadingSquare_coeff_181
  recurrence4LeadingSquare_coeff_182
  recurrence4LeadingSquare_coeff_183
  recurrence4LeadingSquare_coeff_184
  recurrence4LeadingSquare_coeff_185
  recurrence4LeadingSquare_coeff_186
  recurrence4LeadingSquare_coeff_187
  recurrence4LeadingSquare_coeff_188
  recurrence4LeadingSquare_coeff_189
  recurrence4LeadingSquare_coeff_190
  recurrence4LeadingSquare_coeff_191
  recurrence4LeadingSquare_coeff_192
  recurrence4LeadingSquare_coeff_193
  recurrence4LeadingSquare_coeff_194
  recurrence4LeadingSquare_coeff_195
  recurrence4LeadingSquare_coeff_196
  recurrence4LeadingSquare_coeff_197
  recurrence4LeadingSquare_coeff_198
  recurrence4LeadingSquare_coeff_199
  recurrence4LeadingSquare_coeff_200
  recurrence4LeadingSquare_coeff_201
  recurrence4LeadingSquare_coeff_202
  recurrence4LeadingSquare_coeff_203
  recurrence4LeadingSquare_coeff_204
  recurrence4LeadingSquare_coeff_205
  recurrence4LeadingSquare_coeff_206

attribute [local simp]
  recurrence4LeadingSquare_coeff_207
  recurrence4LeadingSquare_coeff_208
  recurrence4LeadingSquare_coeff_209
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_220
  recurrence4LeadingSquare_coeff_221
  recurrence4LeadingSquare_coeff_222
  recurrence4LeadingSquare_coeff_223
  recurrence4LeadingSquare_coeff_224
  recurrence4LeadingSquare_coeff_225
  recurrence4LeadingSquare_coeff_226
  recurrence4LeadingSquare_coeff_227
  recurrence4LeadingSquare_coeff_228
  recurrence4LeadingSquare_coeff_229
  recurrence4LeadingSquare_coeff_230
  recurrence4LeadingSquare_coeff_231
  recurrence4LeadingSquare_coeff_232
  recurrence4LeadingSquare_coeff_233
  recurrence4LeadingSquare_coeff_234
  recurrence4LeadingSquare_coeff_235
  recurrence4LeadingSquare_coeff_236
  recurrence4LeadingSquare_coeff_237
  recurrence4LeadingSquare_coeff_238
  recurrence4LeadingSquare_coeff_239
  recurrence4LeadingSquare_coeff_240
  recurrence4LeadingSquare_coeff_241
  recurrence4LeadingSquare_coeff_242
  recurrence4LeadingSquare_coeff_243
  recurrence4LeadingSquare_coeff_244
  recurrence4LeadingSquare_coeff_245
  recurrence4LeadingSquare_coeff_246
  recurrence4LeadingSquare_coeff_247
  recurrence4LeadingSquare_coeff_248
  recurrence4LeadingSquare_coeff_249
  recurrence4LeadingSquare_coeff_250
  recurrence4LeadingSquare_coeff_251
  recurrence4LeadingSquare_coeff_252
  recurrence4LeadingSquare_coeff_253
  recurrence4LeadingSquare_coeff_254
  recurrence4LeadingSquare_coeff_255
  recurrence4LeadingSquare_coeff_256
  recurrence4LeadingSquare_coeff_257
  recurrence4LeadingSquare_coeff_258
  recurrence4LeadingSquare_coeff_259
  recurrence4LeadingSquare_coeff_260
  recurrence4LeadingSquare_coeff_261
  recurrence4LeadingSquare_coeff_262
  recurrence4LeadingSquare_coeff_263
  recurrence4LeadingSquare_coeff_264
  recurrence4LeadingSquare_coeff_265
  recurrence4LeadingSquare_coeff_266
  recurrence4LeadingSquare_coeff_267
  recurrence4LeadingSquare_coeff_268
  recurrence4LeadingSquare_coeff_269
  recurrence4LeadingSquare_coeff_270

attribute [local simp]
  recurrence4LeadingSquare_coeff_271
  recurrence4LeadingSquare_coeff_272
  recurrence4LeadingSquare_coeff_273
  recurrence4LeadingSquare_coeff_274
  recurrence4LeadingSquare_coeff_275
  recurrence4LeadingSquare_coeff_276
  recurrence4LeadingSquare_coeff_277
  recurrence4LeadingSquare_coeff_278
  recurrence4LeadingSquare_coeff_279
  recurrence4LeadingSquare_coeff_280
  recurrence4LeadingSquare_coeff_281
  recurrence4LeadingSquare_coeff_282
  recurrence4LeadingSquare_coeff_283
  recurrence4LeadingSquare_coeff_284
  recurrence4LeadingSquare_coeff_285
  recurrence4LeadingSquare_coeff_286
  recurrence4LeadingSquare_coeff_287
  recurrence4LeadingSquare_coeff_288
  recurrence4LeadingSquare_coeff_289
  recurrence4LeadingSquare_coeff_290
  recurrence4LeadingSquare_coeff_291
  recurrence4LeadingSquare_coeff_292
  recurrence4LeadingSquare_coeff_293
  recurrence4LeadingSquare_coeff_294
  recurrence4LeadingSquare_coeff_295
  recurrence4LeadingSquare_coeff_296
  recurrence4LeadingSquare_coeff_297
  recurrence4LeadingSquare_coeff_298
  recurrence4LeadingSquare_coeff_299
  recurrence4LeadingSquare_coeff_300
  recurrence4LeadingSquare_coeff_301
  recurrence4LeadingSquare_coeff_302
  recurrence4LeadingSquare_coeff_303
  recurrence4LeadingSquare_coeff_304
  recurrence4LeadingSquare_coeff_305
  recurrence4LeadingSquare_coeff_306
  recurrence4LeadingSquare_coeff_307
  recurrence4LeadingSquare_coeff_308
  recurrence4LeadingSquare_coeff_309
  recurrence4LeadingSquare_coeff_310
  recurrence4LeadingSquare_coeff_311
  recurrence4LeadingSquare_coeff_312
  recurrence4LeadingSquare_coeff_313
  recurrence4LeadingSquare_coeff_314
  recurrence4LeadingSquare_coeff_315
  recurrence4LeadingSquare_coeff_316
  recurrence4LeadingSquare_coeff_317
  recurrence4LeadingSquare_coeff_318
  recurrence4LeadingSquare_coeff_319
  recurrence4LeadingSquare_coeff_320
  recurrence4LeadingSquare_coeff_321
  recurrence4LeadingSquare_coeff_322
  recurrence4LeadingSquare_coeff_323
  recurrence4LeadingSquare_coeff_324
  recurrence4LeadingSquare_coeff_325
  recurrence4LeadingSquare_coeff_326
  recurrence4LeadingSquare_coeff_327
  recurrence4LeadingSquare_coeff_328

private theorem recurrence4Scalar2Left_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (433 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_433 :
    recurrence4Scalar2Left.coeff 433 =
      ((((244857973921286128882791047080303530771 * 10 ^ 70 +
        3643603392798810437252986679496734048858010057772849715353325830194864) * 10 ^ 70 +
        9395858937915070980090858719875929318231044168839495529890638973222420) * 10 ^ 70 +
        6729038284752113022364515775617409464301365046981242193379766290156991) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (433 - x)) = _
  rw [show 434 = 247 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 18 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (434 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_434 :
    recurrence4Scalar2Left.coeff 434 =
      -((((108770027275399426401931260369832576951 * 10 ^ 70 +
        7794409692855535966183875352406638918978071158230306279613641348905657) * 10 ^ 70 +
        6756788542988497490839151479470168814201710536855365425445069261116929) * 10 ^ 70 +
        7757105375398512780750885760083207342487537668949416552986384318005135) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (434 - x)) = _
  rw [show 435 = 248 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 17 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (435 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_435 :
    recurrence4Scalar2Left.coeff 435 =
      ((((36390089365785479015045692416453643188 * 10 ^ 70 +
        5203193404579713167530785937493767479438911421446003944391027569201998) * 10 ^ 70 +
        8013200759830146911646481728103773561740670762831064422718820414777731) * 10 ^ 70 +
        1301400858588347946859237734126410242877584003897524894466070735865815) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (435 - x)) = _
  rw [show 436 = 249 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 16 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (436 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_436 :
    recurrence4Scalar2Left.coeff 436 =
      -((((10507236258510291726465354828124268781 * 10 ^ 70 +
        9813609142627558688552402465248899017650152840757730133417997049814357) * 10 ^ 70 +
        2978064772845870887666273879365631326894019134778560063074046522373764) * 10 ^ 70 +
        4184917650136564045947132037673979708994640088498778888533165401585322) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (436 - x)) = _
  rw [show 437 = 250 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 15 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (437 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_437 :
    recurrence4Scalar2Left.coeff 437 =
      ((((2737135914561965601530245204498934309 * 10 ^ 70 +
        6069114745368280056603194150257405828735332427837133961473177687778165) * 10 ^ 70 +
        6365364589371818807975571411588532249450668934717993222035795283301566) * 10 ^ 70 +
        4028159804728396727755776541117140318114790117756266796868702020372776) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (437 - x)) = _
  rw [show 438 = 251 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 14 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (438 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_438 :
    recurrence4Scalar2Left.coeff 438 =
      -((((655559400858226313292605653768815265 * 10 ^ 70 +
        6584240500416062464586115892015282407245812007087094576608222394356411) * 10 ^ 70 +
        2640344714142582777450063867315965697677439208120452267664510149405974) * 10 ^ 70 +
        5718126615919028116101917078661384772569901608266819529674338711254728) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (438 - x)) = _
  rw [show 439 = 252 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 13 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (439 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_439 :
    recurrence4Scalar2Left.coeff 439 =
      ((((145602557772450920258604809693012914 * 10 ^ 70 +
        3785761936534684596683724854693228271008685643331447660894433601089293) * 10 ^ 70 +
        4484417602739051491499752511091749968018284986688255701683585275650117) * 10 ^ 70 +
        1607711969635203654445830973928602158024267425013856999370232655445682) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (439 - x)) = _
  rw [show 440 = 253 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 12 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (440 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_440 :
    recurrence4Scalar2Left.coeff 440 =
      -((((30086290218814662587956104952054903 * 10 ^ 70 +
        8472928923867647910154310808342797944094540400219320298008743595138866) * 10 ^ 70 +
        1065225915164592237756179201707785347083143732084687208222705837025378) * 10 ^ 70 +
        6313938470544652389732480798014344772514853232930916891031657536189963) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (440 - x)) = _
  rw [show 441 = 254 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 11 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (441 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_441 :
    recurrence4Scalar2Left.coeff 441 =
      ((((5781568149269423938867536152279338 * 10 ^ 70 +
        9517053505847482506066775326402202821613165756253861519898230680115625) * 10 ^ 70 +
        9393154049144597425882689513141097184255466261240869561813668788092459) * 10 ^ 70 +
        9496401147058651529138392397347984977286299249975386987304017642322771) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (441 - x)) = _
  rw [show 442 = 255 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 10 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (442 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_442 :
    recurrence4Scalar2Left.coeff 442 =
      -((((1029489477725073053895473184963298 * 10 ^ 70 +
        9362050127693988419486261080631317948663268985258898855234244945696371) * 10 ^ 70 +
        6536150925415534719400142357445927083967826199541687736266366876742870) * 10 ^ 70 +
        1983343180045386012335427625499806332718199052384007585415329188748461) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (442 - x)) = _
  rw [show 443 = 256 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 9 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (443 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_443 :
    recurrence4Scalar2Left.coeff 443 =
      ((((168572755922375647841859210333753 * 10 ^ 70 +
        9340005217287166224867320989404283799961135146720986485246850865261696) * 10 ^ 70 +
        3605765832426339526121382345334496189656984759433678812109078655477468) * 10 ^ 70 +
        0180455053055888267963263252995802819145765117585701591185117573711779) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (443 - x)) = _
  rw [show 444 = 257 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 8 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (444 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_444 :
    recurrence4Scalar2Left.coeff 444 =
      -((((25029659532904333649476350978613 * 10 ^ 70 +
        6105082933457370051527697800765194308349885493368970232542077465772712) * 10 ^ 70 +
        1546399727006276437279945216674477137511167339567627959793132395226100) * 10 ^ 70 +
        2712806076828690650239104859057542611392389234390456142336733269775958) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (444 - x)) = _
  rw [show 445 = 258 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 7 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (445 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_445 :
    recurrence4Scalar2Left.coeff 445 =
      ((((3280242475819258281657725471360 * 10 ^ 70 +
        7580503205311419255083746137833385764612866073952295853819928814054520) * 10 ^ 70 +
        0607078538867935197666004973162096382372386818440769506441189170536224) * 10 ^ 70 +
        3417823883751788969246719433100994645842926293458924378580230107334940) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (445 - x)) = _
  rw [show 446 = 259 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 6 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (446 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_446 :
    recurrence4Scalar2Left.coeff 446 =
      -((((356874590095574098078731083728 * 10 ^ 70 +
        4557062487353632587142892975537569828305994413190773987024144430328633) * 10 ^ 70 +
        5650069375852594905093166104063286229673349209297271604829122665519641) * 10 ^ 70 +
        7076200780895418976738683482114971460810650949733021311897675720134633) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (446 - x)) = _
  rw [show 447 = 260 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 5 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (447 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_447 :
    recurrence4Scalar2Left.coeff 447 =
      ((((26279921571167459537796825670 * 10 ^ 70 +
        1606652562477943229816438703956620800692394292089258969884273971634424) * 10 ^ 70 +
        6397510894983794900463026628264148512695362969329893985218938834522049) * 10 ^ 70 +
        0990934723888325887082010114926847034937052153226382874870772214274358) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (447 - x)) = _
  rw [show 448 = 261 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 4 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (448 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_448 :
    recurrence4Scalar2Left.coeff 448 =
      ((((479697964311174565542602172 * 10 ^ 70 +
        3783199075403823121245281125732660615961365773001611976642666981630487) * 10 ^ 70 +
        5865650271267530593793783947303778295145770774938881346550186339048380) * 10 ^ 70 +
        8301917531988218879121367289189045667941937525379385991571543727814226) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (448 - x)) = _
  rw [show 449 = 262 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 3 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (449 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_449 :
    recurrence4Scalar2Left.coeff 449 =
      -((((656133061299634177993419894 * 10 ^ 70 +
        5998129961111324247985337496965544639163758595867185760066552991529269) * 10 ^ 70 +
        3543626271952447749742211340569333698256188616538598843943105613592893) * 10 ^ 70 +
        7061703571086828982643416240857540829226227197809589144567220299389826) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (449 - x)) = _
  rw [show 450 = 263 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 2 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (450 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_450 :
    recurrence4Scalar2Left.coeff 450 =
      ((((157092477577848120427454062 * 10 ^ 70 +
        5950925936388784920134300102095054841997306471239060564537253971712701) * 10 ^ 70 +
        4272577961086020118106026818386726962140050397098121026527860242629848) * 10 ^ 70 +
        6379386569858144525108677654612142764097672359632789401735321053899079) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (450 - x)) = _
  rw [show 451 = 264 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 1 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (451 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_451 :
    recurrence4Scalar2Left.coeff 451 =
      -((((26610476783237604383142834 * 10 ^ 70 +
        5515186227201519897583964653594149397701584912897089389819745016297960) * 10 ^ 70 +
        2149400182123046138500819174810753272788926362287555601204613770567912) * 10 ^ 70 +
        5784729722155269302046665002485765146333027879102280812280780781973819) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (451 - x)) = _
  rw [show 452 = 265 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (452 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_452 :
    recurrence4Scalar2Left.coeff 452 =
      ((((3612475393548972481552048 * 10 ^ 70 +
        9916843114746303110162741599273444653617152505518655143147570989788190) * 10 ^ 70 +
        9579014829388419264149605702728359868237052351374944387278821835567224) * 10 ^ 70 +
        0469623625416580859464386312363742242815119416433516872242677839622349) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (452 - x)) = _
  rw [show 453 = 266 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 31 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (453 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_453 :
    recurrence4Scalar2Left.coeff 453 =
      -((((396384754952312783774800 * 10 ^ 70 +
        4618274370694882244088828074429688422839660610023959952526105213820141) * 10 ^ 70 +
        8627596164662228843062398345563677858418736526846635185678394788002291) * 10 ^ 70 +
        3446437198392789145611792014007400247142026920996702469299915286072566) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (453 - x)) = _
  rw [show 454 = 267 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 30 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (454 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_454 :
    recurrence4Scalar2Left.coeff 454 =
      ((((32535676168496441201324 * 10 ^ 70 +
        4049914642448452502919929067074521138341269987498146854937110427728780) * 10 ^ 70 +
        6291394334869141176716216704739663795280748599693237289484888318407901) * 10 ^ 70 +
        4293772439239529811179545748398056848628282823326127653254694989822000) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (454 - x)) = _
  rw [show 455 = 268 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 29 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (455 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_455 :
    recurrence4Scalar2Left.coeff 455 =
      -((((1255575505533262477172 * 10 ^ 70 +
        6623718473261454583919643805723285003232442236896785155133777395676271) * 10 ^ 70 +
        0285212136123907910794827569350848986161065612049705809924721485176701) * 10 ^ 70 +
        0387827117920143179258904318883446408029543709852147571949931666209784) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (455 - x)) = _
  rw [show 456 = 269 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 28 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (456 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_456 :
    recurrence4Scalar2Left.coeff 456 =
      -((((179836074289554000156 * 10 ^ 70 +
        8509920584764508671944286705061279822853149731913236467018993449755644) * 10 ^ 70 +
        2048442724796566060182923871992875217131204619551467898787089268169817) * 10 ^ 70 +
        6000645207262154282708711193719045285459330036592415045362581949792323) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (456 - x)) = _
  rw [show 457 = 270 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 27 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (457 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_457 :
    recurrence4Scalar2Left.coeff 457 =
      ((((51600506174003621026 * 10 ^ 70 +
        0097512666465292667900290705596294933224156591739109683972724285791518) * 10 ^ 70 +
        4433658588430544275991933254585261860579582992512403083835832932220250) * 10 ^ 70 +
        3707307089734486246393512960211710745396505823837980989880224166647207) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (457 - x)) = _
  rw [show 458 = 271 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 26 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (458 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_458 :
    recurrence4Scalar2Left.coeff 458 =
      -((((7776987944088435849 * 10 ^ 70 +
        5103199646060860379370591437701642319658387429018190283861011501615568) * 10 ^ 70 +
        5960932466954338464443942871415929026082288839177374573740926823940798) * 10 ^ 70 +
        1695439751542229515043372721372109836847612582688408517892171973038657) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (458 - x)) = _
  rw [show 459 = 272 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 25 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (459 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_459 :
    recurrence4Scalar2Left.coeff 459 =
      ((((873518243253726487 * 10 ^ 70 +
        4756829098503031195142832185527750842938340890203895541586222338386137) * 10 ^ 70 +
        3727834088785353505412994375575879413400146680041620420813934836878107) * 10 ^ 70 +
        9530835731746400678545619540041750243908483337504517139437848595532445) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (459 - x)) = _
  rw [show 460 = 273 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 24 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (460 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_460 :
    recurrence4Scalar2Left.coeff 460 =
      -((((77176331542928346 * 10 ^ 70 +
        1845022550509563754894219588692459401666768163588798819141349087803195) * 10 ^ 70 +
        3388096902413920839788455458946719360873454334829910838331142195814649) * 10 ^ 70 +
        3329691709835002211738849332038032685290773661357231744319978158676434) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (460 - x)) = _
  rw [show 461 = 274 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 23 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
