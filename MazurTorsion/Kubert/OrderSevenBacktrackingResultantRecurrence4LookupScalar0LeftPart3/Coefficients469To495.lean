/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart3Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_100
  recurrence4A0_coeff_101
  recurrence4A0_coeff_102
  recurrence4A0_coeff_103
  recurrence4A0_coeff_104
  recurrence4A0_coeff_105
  recurrence4A0_coeff_106
  recurrence4A0_coeff_107
  recurrence4A0_coeff_108
  recurrence4A0_coeff_109
  recurrence4A0_coeff_110
  recurrence4A0_coeff_111
  recurrence4A0_coeff_112
  recurrence4A0_coeff_113
  recurrence4A0_coeff_114
  recurrence4A0_coeff_115
  recurrence4A0_coeff_116
  recurrence4A0_coeff_117
  recurrence4A0_coeff_118
  recurrence4A0_coeff_119
  recurrence4A0_coeff_120
  recurrence4A0_coeff_121
  recurrence4A0_coeff_122
  recurrence4A0_coeff_123
  recurrence4A0_coeff_124
  recurrence4A0_coeff_125
  recurrence4A0_coeff_126
  recurrence4A0_coeff_127
  recurrence4A0_coeff_128
  recurrence4A0_coeff_129
  recurrence4A0_coeff_130
  recurrence4A0_coeff_131
  recurrence4A0_coeff_132
  recurrence4A0_coeff_133
  recurrence4A0_coeff_134
  recurrence4A0_coeff_135
  recurrence4A0_coeff_136
  recurrence4A0_coeff_137
  recurrence4A0_coeff_138
  recurrence4A0_coeff_139
  recurrence4A0_coeff_140
  recurrence4A0_coeff_141
  recurrence4A0_coeff_142
  recurrence4A0_coeff_143
  recurrence4A0_coeff_144
  recurrence4A0_coeff_145
  recurrence4A0_coeff_146
  recurrence4A0_coeff_147
  recurrence4A0_coeff_148
  recurrence4A0_coeff_149
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_163

attribute [local simp]
  recurrence4A0_coeff_164
  recurrence4A0_coeff_165
  recurrence4A0_coeff_166
  recurrence4A0_coeff_167
  recurrence4A0_coeff_168
  recurrence4A0_coeff_169
  recurrence4A0_coeff_170
  recurrence4A0_coeff_171
  recurrence4A0_coeff_172
  recurrence4A0_coeff_173
  recurrence4A0_coeff_174
  recurrence4A0_coeff_175
  recurrence4A0_coeff_176
  recurrence4A0_coeff_177
  recurrence4A0_coeff_178
  recurrence4A0_coeff_179
  recurrence4A0_coeff_180
  recurrence4A0_coeff_181
  recurrence4A0_coeff_182
  recurrence4A0_coeff_183
  recurrence4A0_coeff_184
  recurrence4A0_coeff_185
  recurrence4A0_coeff_186
  recurrence4A0_coeff_187
  recurrence4A0_coeff_188
  recurrence4A0_coeff_189
  recurrence4A0_coeff_190
  recurrence4A0_coeff_191
  recurrence4A0_coeff_192
  recurrence4A0_coeff_193
  recurrence4A0_coeff_194
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
  recurrence4A0_coeff_50
  recurrence4A0_coeff_51
  recurrence4A0_coeff_52
  recurrence4A0_coeff_53
  recurrence4A0_coeff_54
  recurrence4A0_coeff_55
  recurrence4A0_coeff_56
  recurrence4A0_coeff_57
  recurrence4A0_coeff_58
  recurrence4A0_coeff_59
  recurrence4A0_coeff_60
  recurrence4A0_coeff_61
  recurrence4A0_coeff_62
  recurrence4A0_coeff_63
  recurrence4A0_coeff_64
  recurrence4A0_coeff_65
  recurrence4A0_coeff_66
  recurrence4A0_coeff_67
  recurrence4A0_coeff_68
  recurrence4A0_coeff_69
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75

attribute [local simp]
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
  recurrence4A0_coeff_80
  recurrence4A0_coeff_81
  recurrence4A0_coeff_82
  recurrence4A0_coeff_83
  recurrence4A0_coeff_84
  recurrence4A0_coeff_85
  recurrence4A0_coeff_86
  recurrence4A0_coeff_87
  recurrence4A0_coeff_88
  recurrence4A0_coeff_89
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar0Left_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (469 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (469 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_469 :
    recurrence4Scalar0Left.coeff 469 =
      ((((67295946039003 * 10 ^ 70 +
        0844097784275154244335786826293716110270645615237997380244163719335400) * 10 ^ 70 +
        7962693227408833736117736806086609865125093247661756202174061671694133) * 10 ^ 70 +
        4005766898249020729462046015221988997088625931779659905900077965271513) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (469 - x)) = _
  rw [show 470 = 275 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 22 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_469_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (470 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (470 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_470 :
    recurrence4Scalar0Left.coeff 470 =
      -((((5561735172591 * 10 ^ 70 +
        6991803300464807857004844057669085041803018862143034079934840621138410) * 10 ^ 70 +
        5169870252684151767256598167090676943525817525389926281274012958183564) * 10 ^ 70 +
        3940102466244136981703201698514212950562935565524379389477993247119406) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (470 - x)) = _
  rw [show 471 = 276 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 21 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_470_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (471 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (471 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_471 :
    recurrence4Scalar0Left.coeff 471 =
      ((((313169660239 * 10 ^ 70 +
        2415242682721386231949491649319130177017309470822156180193336645990369) * 10 ^ 70 +
        3503045046149735716021904976616450850107066139133538221728486751089791) * 10 ^ 70 +
        1626353817348396316089001033317639359795414438705306028875849518120205) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (471 - x)) = _
  rw [show 472 = 277 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 20 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_471_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (472 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (472 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_472 :
    recurrence4Scalar0Left.coeff 472 =
      -((((8008891939 * 10 ^ 70 +
        3105241360475623339605635784429957903712950658216061049597081836412185) * 10 ^ 70 +
        8215785866501417548441532993159286963907117775023933503188958996302780) * 10 ^ 70 +
        9228160891359970676533694120870243599050460298289186385376669247974627) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (472 - x)) = _
  rw [show 473 = 278 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 19 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_472_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (473 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (473 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_473 :
    recurrence4Scalar0Left.coeff 473 =
      -((((581291110 * 10 ^ 70 +
        8405127621534616926512715224914521490916544477747628618839971801097625) * 10 ^ 70 +
        8486354794814021516448253114610927115173076734436458947173886334086794) * 10 ^ 70 +
        7332850109314882735300143615378001195328557634783288063175462715993153) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (473 - x)) = _
  rw [show 474 = 279 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 18 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_473_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (474 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (474 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_474 :
    recurrence4Scalar0Left.coeff 474 =
      ((((92692879 * 10 ^ 70 +
        2065568019679674306660030210715906204222363115024592159220038746835151) * 10 ^ 70 +
        7519383118875692851171393479117343515870487841515470388092686246514333) * 10 ^ 70 +
        8125387981575230239730509086132395153299099605815197143875886970227281) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (474 - x)) = _
  rw [show 475 = 280 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 17 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_474_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (475 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (475 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_475 :
    recurrence4Scalar0Left.coeff 475 =
      -((((6626454 * 10 ^ 70 +
        7031517461407010783162408190200706002702652197845523734190012549702285) * 10 ^ 70 +
        5709874983433849557270938978829477151826763855408229960563300961524896) * 10 ^ 70 +
        3080555385399087653858849001491854537472552650312242752939041420258702) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (475 - x)) = _
  rw [show 476 = 281 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 16 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_475_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (476 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (476 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_476 :
    recurrence4Scalar0Left.coeff 476 =
      ((((280730 * 10 ^ 70 +
        5714908015524029617894156850788806029048216605082771826160619747955792) * 10 ^ 70 +
        4004352041320263973303741183235397356487448821334930498577962769493415) * 10 ^ 70 +
        1599909387582623663282473083584065006165695839781799496458050799094099) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (476 - x)) = _
  rw [show 477 = 282 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 15 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_476_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (477 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (477 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_477 :
    recurrence4Scalar0Left.coeff 477 =
      -((((4386 * 10 ^ 70 +
        3046300408515753658634717964974486726689451386941989552388290598907813) * 10 ^ 70 +
        9409857899868820172630604938271222672252082332257435506506855587595385) * 10 ^ 70 +
        5246609229079101603490517677769016079228093706429956215759370500353872) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (477 - x)) = _
  rw [show 478 = 283 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 14 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_477_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (478 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (478 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_478 :
    recurrence4Scalar0Left.coeff 478 =
      -((((297 * 10 ^ 70 +
        4387354168856717307210790375011282658253434766163187103996349293972089) * 10 ^ 70 +
        6539101056253492859595213684817265127920401889622518631578780995935058) * 10 ^ 70 +
        4398881849333732464170388378688260532454093358824224601423998137564004) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (478 - x)) = _
  rw [show 479 = 284 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 13 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (479 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (479 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_479 :
    recurrence4Scalar0Left.coeff 479 =
      ((((24 * 10 ^ 70 +
        5448390286743848926879973845335907467419056467622665248952849065103155) * 10 ^ 70 +
        2412481339578081713163001583361981414562646879291524368686410830161223) * 10 ^ 70 +
        4686162220945946882350451663456856846977646856186864814190883167423305) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (479 - x)) = _
  rw [show 480 = 285 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 12 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (480 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (480 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_480 :
    recurrence4Scalar0Left.coeff 480 =
      -(((7855100487692189057980541581178155324710357790221247111242879626160669 * 10 ^ 70 +
        5095706491500903423422870143464168782991019250305440800157919644313178) * 10 ^ 70 +
        7896367610498568860794420315949034970085357142543877743580527707908601) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (480 - x)) = _
  rw [show 481 = 286 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 11 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (481 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (481 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_481 :
    recurrence4Scalar0Left.coeff 481 =
      (((50684834629015929140593752431839633593989032693360468518308518444801 * 10 ^ 70 +
        9798536951660501691891211577917373962157611366003155472574743563002137) * 10 ^ 70 +
        0857106964486284840930284713532096929504151872472226131435768791300366) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (481 - x)) = _
  rw [show 482 = 287 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 10 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (482 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (482 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_482 :
    recurrence4Scalar0Left.coeff 482 =
      (((4904427523839015532552993118886741826425509160621649689423249504037 * 10 ^ 70 +
        0675466392425254384869265819544218094786515292207660817076326196880420) * 10 ^ 70 +
        3760709276473224849281172205782494710623824080494901813603497058600139) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (482 - x)) = _
  rw [show 483 = 288 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 9 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (483 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (483 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_483 :
    recurrence4Scalar0Left.coeff 483 =
      -(((150309625013996821451320348142483333946589260101648613527440448385 * 10 ^ 70 +
        0393257686948503524378692770662536310489064633921245255926086976764890) * 10 ^ 70 +
        7615612718098220532328950534620316381148999817123333353723579578551483) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (483 - x)) = _
  rw [show 484 = 289 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 8 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (484 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (484 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_484 :
    recurrence4Scalar0Left.coeff 484 =
      (((254750564118255327796640595640449263193209426476247649027979558 * 10 ^ 70 +
        7466568087494234885882124487110392264879459339814175758217841521718210) * 10 ^ 70 +
        4111117963717202840693984884494621509190059926909708745707711988486528) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (484 - x)) = _
  rw [show 485 = 290 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 7 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (485 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (485 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_485 :
    recurrence4Scalar0Left.coeff 485 =
      (((49482817899931044043935608860411898018440560836313382427439755 * 10 ^ 70 +
        1335669158022181043503399568902326734453151018625758698198969835364668) * 10 ^ 70 +
        5638189277643732979279735881508672996282530686316018604451060192484918) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (485 - x)) = _
  rw [show 486 = 291 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 6 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (486 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (486 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_486 :
    recurrence4Scalar0Left.coeff 486 =
      -(((349936033041434450919264992544415531379995240345588054497836 * 10 ^ 70 +
        4355128287872634153116448029840573859286196986379712167931800774764979) * 10 ^ 70 +
        8729842069312097697790513656918077721628280147348628605225881916327909) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (486 - x)) = _
  rw [show 487 = 292 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 5 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (487 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (487 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_487 :
    recurrence4Scalar0Left.coeff 487 =
      -(((8009292067724063727728763995028861076959039821913084686443 * 10 ^ 70 +
        7894234632380386649193272372667956936804509312153403766903071698596015) * 10 ^ 70 +
        1183426279297093644884094776145061628168905279224697521105976036721026) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (487 - x)) = _
  rw [show 488 = 293 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 4 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (488 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (488 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_488 :
    recurrence4Scalar0Left.coeff 488 =
      (((44249746854841121594858438321797120471763354516530881381 * 10 ^ 70 +
        9798922800912183638643606597482332821351388032367474579281528843948925) * 10 ^ 70 +
        9805063935236248788310622892520902704695164833208765233936459253061799) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (488 - x)) = _
  rw [show 489 = 294 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 3 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (489 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (489 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_489 :
    recurrence4Scalar0Left.coeff 489 =
      (((783014121696740927730181211175224039994545530622311959 * 10 ^ 70 +
        4265931792810080690365007178796401522036565528336235619668718949039138) * 10 ^ 70 +
        8668229579019136904292673705588869078782320874252001182349978481892647) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (489 - x)) = _
  rw [show 490 = 295 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 2 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_490_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (490 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (490 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_490_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (490 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (490 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_490 :
    recurrence4Scalar0Left.coeff 490 =
      -(((1138635058114832384965231398698596940685794577402644 * 10 ^ 70 +
        2385238316710298044426396478856480069635966415718358693872121479149769) * 10 ^ 70 +
        4962145534534821709768905062145675011127661439818380728463037234251893) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 491,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (490 - x)) = _
  rw [show 491 = 296 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 1 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_490_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_490_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_491_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (491 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (491 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_491_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (491 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (491 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_491 :
    recurrence4Scalar0Left.coeff 491 =
      -(((35775286253420776269925170365385717793897803020760 * 10 ^ 70 +
        7642362877842140072979859022708701304162452953167317492064866075938394) * 10 ^ 70 +
        8473531964922768395838553652202552907334192679363179370226410109589700) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 492,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (491 - x)) = _
  rw [show 492 = 297 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_491_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_491_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_492_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (492 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (492 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_492_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (492 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (492 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_492 :
    recurrence4Scalar0Left.coeff 492 =
      -(((23567290547925269018533861970483944602407422853 * 10 ^ 70 +
        8150175931111597318861770092274973964562775908768654539609168334359638) * 10 ^ 70 +
        9763383394149307773234013607247565186515175828834026533850744612460248) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 493,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (492 - x)) = _
  rw [show 493 = 298 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 31 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_492_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_492_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_493_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (493 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (493 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_493_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (493 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (493 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_493 :
    recurrence4Scalar0Left.coeff 493 =
      (((793242936866685633456941951755959560326643304 * 10 ^ 70 +
        3285392574685861098906082533987212433404949985228487475137313040669519) * 10 ^ 70 +
        2801267701960411577485327750317138292095327530210608343510097455700587) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 494,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (493 - x)) = _
  rw [show 494 = 299 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 30 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_493_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_493_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_494_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (494 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (494 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_494_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (494 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (494 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_494 :
    recurrence4Scalar0Left.coeff 494 =
      (((1284441353887641185573380580416375429976284 * 10 ^ 70 +
        3803522633470523221617243974876765117930041191016258541474725884454811) * 10 ^ 70 +
        6810390620356445232871279706016668033860224888123457954184145985034194) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 495,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (494 - x)) = _
  rw [show 495 = 300 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 29 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_494_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_494_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_495_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (495 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (495 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_495_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (495 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (495 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_495 :
    recurrence4Scalar0Left.coeff 495 =
      -(((9177361673499818256163173086407211532381 * 10 ^ 70 +
        4381488151271587037312918191706309715669247642753357460800014966274402) * 10 ^ 70 +
        3158698627483204223627468072724178487372370103808371210383333867970462) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 496,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (495 - x)) = _
  rw [show 496 = 301 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 28 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_495_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_495_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
