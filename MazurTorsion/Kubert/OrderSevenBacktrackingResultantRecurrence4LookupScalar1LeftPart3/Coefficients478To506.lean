/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_163

attribute [local simp]
  recurrence4A1_coeff_164
  recurrence4A1_coeff_165
  recurrence4A1_coeff_166
  recurrence4A1_coeff_167
  recurrence4A1_coeff_168
  recurrence4A1_coeff_169
  recurrence4A1_coeff_170
  recurrence4A1_coeff_171
  recurrence4A1_coeff_172
  recurrence4A1_coeff_173
  recurrence4A1_coeff_174
  recurrence4A1_coeff_175
  recurrence4A1_coeff_176
  recurrence4A1_coeff_177
  recurrence4A1_coeff_178
  recurrence4A1_coeff_179
  recurrence4A1_coeff_180
  recurrence4A1_coeff_181
  recurrence4A1_coeff_182
  recurrence4A1_coeff_183
  recurrence4A1_coeff_184
  recurrence4A1_coeff_185
  recurrence4A1_coeff_186
  recurrence4A1_coeff_187
  recurrence4A1_coeff_188
  recurrence4A1_coeff_189
  recurrence4A1_coeff_190
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68
  recurrence4A1_coeff_69
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86

attribute [local simp]
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar1Left_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (478 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (478 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_478 :
    recurrence4Scalar1Left.coeff 478 =
      (((76617927338143601076825142693165744610855350449059046463371295680849 * 10 ^ 70 +
        1173309816077408705403503732007686745621895623882019848969756322946079) * 10 ^ 70 +
        2145580332853503076037999789227163269955799088769090188485447995366531) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (478 - x)) = _
  rw [show 479 = 288 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 9 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (479 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (479 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_479 :
    recurrence4Scalar1Left.coeff 479 =
      -(((1903232558365977745222195094334596286068933784794014069703181238874 * 10 ^ 70 +
        8527881407487113734056431791885254483043366718434783127890829125446131) * 10 ^ 70 +
        4739467666082295720646659415787364385220724512059180895457130378020247) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (479 - x)) = _
  rw [show 480 = 289 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 8 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (480 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (480 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_480 :
    recurrence4Scalar1Left.coeff 480 =
      -(((2311767725272703510138868364452838540214811436092215305279729634 * 10 ^ 70 +
        1566518647150925547777756137340240582491756114759222120836996644527462) * 10 ^ 70 +
        2351380421572136047098427771824784070488969940561033353836973464764369) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (480 - x)) = _
  rw [show 481 = 290 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 7 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (481 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (481 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_481 :
    recurrence4Scalar1Left.coeff 481 =
      (((681042433537116011461936400373663486544812855945356435088444202 * 10 ^ 70 +
        3795053574652591827965978618172513526129631382791731625611759580532967) * 10 ^ 70 +
        7317384426980898857937558372873014926388156086531206817517254799332631) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (481 - x)) = _
  rw [show 482 = 291 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 6 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (482 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (482 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_482 :
    recurrence4Scalar1Left.coeff 482 =
      -(((3620201332789129908964410227332555084202802584981366240567240 * 10 ^ 70 +
        6644444125761547334851360324975201145562115428042947921245032567854212) * 10 ^ 70 +
        0929404223890537842107572338585150382162972183647217234221580063981464) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (482 - x)) = _
  rw [show 483 = 292 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 5 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (483 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (483 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_483 :
    recurrence4Scalar1Left.coeff 483 =
      -(((112277351554154146029971104357264501218295061252552485274746 * 10 ^ 70 +
        4941379643852247214267758098604587426397693003752125377547029353150127) * 10 ^ 70 +
        4691651129817395289925322406302388367260695629861924183593504111998155) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (483 - x)) = _
  rw [show 484 = 293 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 4 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (484 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (484 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_484 :
    recurrence4Scalar1Left.coeff 484 =
      (((483896825529224368740682534267589266519101572129919514718 * 10 ^ 70 +
        9641938464366595833681814301462802395219745755907784886964858057301756) * 10 ^ 70 +
        6942837111411385035010976875095087523546848156375534642489112440349742) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (484 - x)) = _
  rw [show 485 = 294 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 3 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (485 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (485 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_485 :
    recurrence4Scalar1Left.coeff 485 =
      (((10823002484764297578795413874523516439038926659097055071 * 10 ^ 70 +
        5198511830924633263821524588512087107345558176655132055402977220256304) * 10 ^ 70 +
        8240807342631573005550889164945059440519341782480576100654667483410979) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (485 - x)) = _
  rw [show 486 = 295 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 2 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (486 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (486 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_486 :
    recurrence4Scalar1Left.coeff 486 =
      -(((9086493520009080072813555404541584083060480326075465 * 10 ^ 70 +
        3621466692458210501447685779640465396370743748071798129393702185881285) * 10 ^ 70 +
        4344662975781279296710983383094641359948895476724402026107567920861190) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (486 - x)) = _
  rw [show 487 = 296 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 1 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (487 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (487 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_487 :
    recurrence4Scalar1Left.coeff 487 =
      -(((488098569552170745584585727183376474238181481777312 * 10 ^ 70 +
        3258837501600606607854506806645887005828711993976709654698913474923003) * 10 ^ 70 +
        1175700883211990100360267324962311444771812190167596442562043379323958) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (487 - x)) = _
  rw [show 488 = 297 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (488 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (488 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_488 :
    recurrence4Scalar1Left.coeff 488 =
      -(((512969154173947504953925736749959694086343295797 * 10 ^ 70 +
        1798345946493874758024304355631635442379708749014018041895019455571946) * 10 ^ 70 +
        4584015045915846467174590008934604903519428473933187664455050384379190) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (488 - x)) = _
  rw [show 489 = 298 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 31 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (489 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (489 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_489 :
    recurrence4Scalar1Left.coeff 489 =
      (((10702863810482982922899521107030863542018343675 * 10 ^ 70 +
        9761104376830142998628781912466458901265031668323550218581925888100175) * 10 ^ 70 +
        9247567666013894815465720182165250166550344716294712964772934386604539) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (489 - x)) = _
  rw [show 490 = 299 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 30 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (490 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (490 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_490 :
    recurrence4Scalar1Left.coeff 490 =
      (((20826703252341907977512952903613860866956332 * 10 ^ 70 +
        3373809806825989188609627331879827481264012924734516317998253004424105) * 10 ^ 70 +
        9563786402942786956281140938145759577381604313205839586250497213245376) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (490 - x)) = _
  rw [show 491 = 300 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 29 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (491 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (491 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_491 :
    recurrence4Scalar1Left.coeff 491 =
      -(((122572172829056251319944553018445367202020 * 10 ^ 70 +
        4531443167970897363002015864071692428173030752131086275833143794066403) * 10 ^ 70 +
        2505504174146451824830207814114612045721804077619448769310963188507117) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (491 - x)) = _
  rw [show 492 = 301 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 28 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (492 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (492 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_492 :
    recurrence4Scalar1Left.coeff 492 =
      -(((269080270014444379375644620052318174761 * 10 ^ 70 +
        2724436497264058935726052869688767046894464683465391283390726858654109) * 10 ^ 70 +
        1378602986226539652667848730663980129395748396872735909516884869316672) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (492 - x)) = _
  rw [show 493 = 302 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 27 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (493 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (493 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_493 :
    recurrence4Scalar1Left.coeff 493 =
      (((864930088125143328797236099854936859 * 10 ^ 70 +
        4449212071870410428286575233567103022645380580596732391134128596037725) * 10 ^ 70 +
        5261361626206944248126085308996602519310369432295196830803106417370020) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (493 - x)) = _
  rw [show 494 = 303 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 26 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (494 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (494 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_494 :
    recurrence4Scalar1Left.coeff 494 =
      (((1634992009730427461628718412101790 * 10 ^ 70 +
        3130940187929764716041065599524067396086959119957562519274925054729441) * 10 ^ 70 +
        2044283424318939762108060859576576458358560735485486714601898135440059) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (494 - x)) = _
  rw [show 495 = 304 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 25 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (495 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (495 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_495 :
    recurrence4Scalar1Left.coeff 495 =
      -(((4066801101171647450358554690058 * 10 ^ 70 +
        6280219180405610278446630003479975693122091035866761939446246148801003) * 10 ^ 70 +
        5509052338760109614571661169920029850625627741010279250994066209296986) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (495 - x)) = _
  rw [show 496 = 305 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 24 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_496_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (496 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (496 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_496_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (496 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (496 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_496 :
    recurrence4Scalar1Left.coeff 496 =
      -(((4549824448185914976154315672 * 10 ^ 70 +
        7333109294712773953668093621060566564814390510393657843523904712911108) * 10 ^ 70 +
        6743317349174297487739667913049258896893823003601407913254345899379740) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 497,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (496 - x)) = _
  rw [show 497 = 306 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 23 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_496_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_496_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_497_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (497 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (497 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_497_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (497 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (497 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_497 :
    recurrence4Scalar1Left.coeff 497 =
      (((11693526468040997849471438 * 10 ^ 70 +
        7561251403231174258533018570541425777176474015486855231744764169527289) * 10 ^ 70 +
        6307948498191759474127323098095148587108601331816849292997160433359208) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 498,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (497 - x)) = _
  rw [show 498 = 307 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 22 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_497_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_497_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_498_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (498 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (498 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_498_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (498 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (498 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_498 :
    recurrence4Scalar1Left.coeff 498 =
      (((3043400530706908746879 * 10 ^ 70 +
        7146079138979986569818496374999971903265115722485976463886497165451738) * 10 ^ 70 +
        7371991053229004212438988163084077685079096320541827176501859953188699) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 499,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (498 - x)) = _
  rw [show 499 = 308 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 21 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_498_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_498_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_499_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (499 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (499 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_499_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (499 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (499 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_499 :
    recurrence4Scalar1Left.coeff 499 =
      -(((14765065397913137520 * 10 ^ 70 +
        2829871521130057125392814156545376428289147416814950040635405692668204) * 10 ^ 70 +
        8131233845113778016822919927741124428196711561370804035005340410299595) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 500,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (499 - x)) = _
  rw [show 500 = 309 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 20 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_499_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_499_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_500_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (500 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (500 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_500_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (500 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (500 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_500 :
    recurrence4Scalar1Left.coeff 500 =
      (((4096177259945854 * 10 ^ 70 +
        0561994973709372331441580909105725500841708185760307680103582380313332) * 10 ^ 70 +
        7326320943905408970799693118316099540943484640481544241546400010379947) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 501,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (500 - x)) = _
  rw [show 501 = 310 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 19 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_500_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_500_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_501_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (501 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (501 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_501_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (501 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (501 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_501 :
    recurrence4Scalar1Left.coeff 501 =
      (((4100236503153 * 10 ^ 70 +
        4563028591500413567847715834609836867469035907121190728779049819991090) * 10 ^ 70 +
        0588892403011822063533653211049258753035875524089637184001037509784159) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 502,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (501 - x)) = _
  rw [show 502 = 311 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 18 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_501_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_501_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_502_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (502 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (502 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_502_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (502 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (502 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_502 :
    recurrence4Scalar1Left.coeff 502 =
      -(((1929208386 * 10 ^ 70 +
        7320123515902100464770449127869507302224751327366322998179999908554082) * 10 ^ 70 +
        3237127582974178648626860623806100429573922207030128731038898193920051) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 503,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (502 - x)) = _
  rw [show 503 = 312 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 17 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_502_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_502_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_503_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (503 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (503 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_503_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (503 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (503 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_503 :
    recurrence4Scalar1Left.coeff 503 =
      -(((16160 * 10 ^ 70 +
        3743361590754193566115413777332267462175651944725778324587212830422544) * 10 ^ 70 +
        3573830177128730040798133491935530859574228933220305089197835646792217) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 504,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (503 - x)) = _
  rw [show 504 = 313 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 16 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_503_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_503_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_504_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (504 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (504 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_504_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (504 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (504 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_504 :
    recurrence4Scalar1Left.coeff 504 =
      (((81 * 10 ^ 70 +
        9326337334966632452168828177338924544436306096197665168304263923139408) * 10 ^ 70 +
        6522482284549335450369409720197746279156164864689850451624191892719438) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 505,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (504 - x)) = _
  rw [show 505 = 314 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 15 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_504_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_504_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_505_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (505 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (505 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_505_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (505 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (505 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_505 :
    recurrence4Scalar1Left.coeff 505 =
      -((73512835015762238232649383817770764141682088569316112889135223020040 * 10 ^ 70 +
        5098786130644309952903187260363657799160192191134302648534064391455705) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 506,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (505 - x)) = _
  rw [show 506 = 315 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 14 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_505_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_505_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_506_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (506 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (506 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_506_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (506 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (506 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_506 :
    recurrence4Scalar1Left.coeff 506 =
      -((2111233048858045200657968856728385218104357508361392142020176247 * 10 ^ 70 +
        6180426832024095620843805339086977293093969483926696777238392473124672) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 507,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (506 - x)) = _
  rw [show 507 = 316 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 13 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_506_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_506_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
