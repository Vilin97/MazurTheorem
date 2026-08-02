/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar1Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (378 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (378 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_378 :
    recurrence4Scalar1Left.coeff 378 =
      -((((5184395983769027852847002975524527465335438398369210784689856552893 * 10 ^ 70 +
        0969372309464475302362329823268433030290153067019765316649732349528792) * 10 ^ 70 +
        0453973447140284967636297861569172310567423085565869613184453143806844) * 10 ^ 70 +
        7124178883419109400006002366099035409960334181266870312408176450720565) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (378 - x)) = _
  rw [show 379 = 188 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 13 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (379 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (379 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_379 :
    recurrence4Scalar1Left.coeff 379 =
      ((((1129574478436834367573346175181540345481205775225292315384252215813 * 10 ^ 70 +
        4052966580433267642352802924314420325687455892843420406748663802730052) * 10 ^ 70 +
        7021661533654289894962659777807590008377719976423763810907234706024603) * 10 ^ 70 +
        9694469115296107643398940286742351076086441462985708979940394080625717) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (379 - x)) = _
  rw [show 380 = 189 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 12 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (380 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (380 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_380 :
    recurrence4Scalar1Left.coeff 380 =
      -((((121028533019063157930345440651346071660720643912405470294585728417 * 10 ^ 70 +
        3083963541625199905810592368894866889974586675012022347671867378100137) * 10 ^ 70 +
        9074323685805730479602792767971815499254407851976569197385885503476452) * 10 ^ 70 +
        5621474938178082636374540965488070614031256701757863897072206938364849) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (380 - x)) = _
  rw [show 381 = 190 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 11 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (381 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (381 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_381 :
    recurrence4Scalar1Left.coeff 381 =
      -((((57370426781855837064215306724523294166299451804097830848873450327 * 10 ^ 70 +
        8339282265932822400134798879773622187031288722455061298772786270919433) * 10 ^ 70 +
        6023875651488252622048826465761931821137809837042939113837989908779100) * 10 ^ 70 +
        4061381243115326642976531694972105091344256056412910099518899356814209) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (381 - x)) = _
  rw [show 382 = 191 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 10 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (382 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (382 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_382 :
    recurrence4Scalar1Left.coeff 382 =
      ((((53071550311904850667919256663173240044298243141606914121888554199 * 10 ^ 70 +
        8928974368025116292605980061079042051789862443425425646299038009156903) * 10 ^ 70 +
        2738696938288784368262468936816882507401645546517867500665539803737050) * 10 ^ 70 +
        0691511927651696380979764687624637321890489759315868738027083892143470) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (382 - x)) = _
  rw [show 383 = 192 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 9 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (383 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (383 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_383 :
    recurrence4Scalar1Left.coeff 383 =
      -((((28373442572871288916716120354684086660041860005961043450676951121 * 10 ^ 70 +
        2931711969488744006667843482529092215975923862210579451397602396121102) * 10 ^ 70 +
        3844910645073010935941938305439600112020506231819777091525269065087851) * 10 ^ 70 +
        9338664821262804088342270539060307364671819712108424975579404691465908) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (383 - x)) = _
  rw [show 384 = 193 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 8 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (384 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (384 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_384 :
    recurrence4Scalar1Left.coeff 384 =
      ((((12433804491818164754279297968569743303502533864650036922072997588 * 10 ^ 70 +
        0672778482156620383489685823236268885146967894049163077234454142790857) * 10 ^ 70 +
        2329062131414605849176293182595432435550728363466334008864914487320239) * 10 ^ 70 +
        1051454334660554200323763124930673969474249513841022938675308855372182) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (384 - x)) = _
  rw [show 385 = 194 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 7 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (385 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (385 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_385 :
    recurrence4Scalar1Left.coeff 385 =
      -((((4828268507577464980642994758652915296528556869432928374630319907 * 10 ^ 70 +
        9426587182209432766775614418133439804650233359259867279787401573065866) * 10 ^ 70 +
        6449905109542131585084477840051458950079451139658903261272296525880015) * 10 ^ 70 +
        3878424037237267831153961690113460771430299774083651059126513988034501) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (385 - x)) = _
  rw [show 386 = 195 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 6 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (386 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (386 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_386 :
    recurrence4Scalar1Left.coeff 386 =
      ((((1704657296331541867004462858263069939288770355168195292653901394 * 10 ^ 70 +
        8876369418313651997991352263579688667112146997387044596426250883088184) * 10 ^ 70 +
        0722272668040573707220819359754722360072851046865943691157518014269714) * 10 ^ 70 +
        8086856986015165128308425280075087185706333256432126508342454150057970) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (386 - x)) = _
  rw [show 387 = 196 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 5 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (387 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (387 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_387 :
    recurrence4Scalar1Left.coeff 387 =
      -((((549309722467978878782192371994894273102602364839814232070036826 * 10 ^ 70 +
        3468015814072826144498516552546834959551441431356986678748966460203058) * 10 ^ 70 +
        6451553485900429400697865066870211542647802351389675303951276314588884) * 10 ^ 70 +
        6134327349850092313053942615630471545166586136439303904343202716145962) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (387 - x)) = _
  rw [show 388 = 197 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 4 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (388 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (388 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_388 :
    recurrence4Scalar1Left.coeff 388 =
      ((((159044801147796498539819130957547826535642765947939561753948391 * 10 ^ 70 +
        3286264525488206853040573960673176006567387302105641122614405868594700) * 10 ^ 70 +
        0583820797948522275307440059900121948081843425909844059006863301958072) * 10 ^ 70 +
        8821946903214517660065174862898230876308880208386339601106378282001349) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (388 - x)) = _
  rw [show 389 = 198 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 3 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (389 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (389 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_389 :
    recurrence4Scalar1Left.coeff 389 =
      -((((39186692599032249784007704964570443393647130411825342329738358 * 10 ^ 70 +
        2155067286111486523008971044143678755154030771580528282418916547588693) * 10 ^ 70 +
        3609922060695214527616017017112027332843435912309189129142949938624960) * 10 ^ 70 +
        5753112530640919655562018215253359411513640141776150162966726744169509) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (389 - x)) = _
  rw [show 390 = 199 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 2 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (390 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (390 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_390 :
    recurrence4Scalar1Left.coeff 390 =
      ((((6666164835367861813806416252754550173595519766680834072890405 * 10 ^ 70 +
        8737670743983788340784901529571715869199840831786667525714188297190970) * 10 ^ 70 +
        9427332373990365355310332218147704565488073843874656944461940870901039) * 10 ^ 70 +
        2858166820314306761183197505890032981286079049077701129565453092693878) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (390 - x)) = _
  rw [show 391 = 200 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 1 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (391 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (391 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_391 :
    recurrence4Scalar1Left.coeff 391 =
      ((((425285582732186555249886375613842322910834452102880648297440 * 10 ^ 70 +
        0369241232486777157760068883591423045285253749233127255158744045489664) * 10 ^ 70 +
        9953781810546924046497949020870048502172182079848795860872742463295532) * 10 ^ 70 +
        1372496979955000489330548183391723710230598940463066258969426992181227) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (391 - x)) = _
  rw [show 392 = 201 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (392 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (392 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_392 :
    recurrence4Scalar1Left.coeff 392 =
      -((((1160734669988461042159423227241626333858937342506088582485801 * 10 ^ 70 +
        2287449372526782385360626520119748752376995220343238625326536201844632) * 10 ^ 70 +
        1567866262375381087126355900263776580925329374552993338413960302193333) * 10 ^ 70 +
        2136284883350671346836528226681884750934471014308588787699761794841790) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (392 - x)) = _
  rw [show 393 = 202 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 31 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (393 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (393 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_393 :
    recurrence4Scalar1Left.coeff 393 =
      ((((757595893636487519216804086458773780341110614856025204236657 * 10 ^ 70 +
        5177781182653635235963376911462006898950775605353631441387683000666650) * 10 ^ 70 +
        6691975986395714764396294304046122679979316823869030095849134053786600) * 10 ^ 70 +
        4975231620311884438575256123616638534333065911311716828303004598004352) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (393 - x)) = _
  rw [show 394 = 203 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 30 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (394 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (394 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_394 :
    recurrence4Scalar1Left.coeff 394 =
      -((((380611221973894335048433900060036262726260755932085488796957 * 10 ^ 70 +
        0610956195486890569519556069200061290651811800800563018441234724164357) * 10 ^ 70 +
        7129301570345686047505279929551860104870209103024622305794926185140240) * 10 ^ 70 +
        6329742336751715360957571066200946475479399967095344398403379579287823) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (394 - x)) = _
  rw [show 395 = 204 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 29 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (395 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (395 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_395 :
    recurrence4Scalar1Left.coeff 395 =
      ((((168761120057167439902959426670529331973435751681045480993932 * 10 ^ 70 +
        9372540741892671232251622667024015384752722119403222205437319163920087) * 10 ^ 70 +
        9123042979880710758760993049219083945350642491621829469175838235862265) * 10 ^ 70 +
        7334600058053116707212243595783873658615520471064093077840035553849746) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (395 - x)) = _
  rw [show 396 = 205 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 28 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (396 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (396 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_396 :
    recurrence4Scalar1Left.coeff 396 =
      -((((69060869301597399130319385471724894682774498149922123458558 * 10 ^ 70 +
        5566724593655040889708485522639918741616154997561828845336876830197764) * 10 ^ 70 +
        8216671448291046091602163552679278130971896591011331631662386853224668) * 10 ^ 70 +
        5294280310255789658869205245401863589341869579179241828513758968031546) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (396 - x)) = _
  rw [show 397 = 206 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 27 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (397 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (397 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_397 :
    recurrence4Scalar1Left.coeff 397 =
      ((((26578454024554951720941904152035330131336076843503960620297 * 10 ^ 70 +
        8246792037587459931949289660159761704056504474208641657321111702868536) * 10 ^ 70 +
        4525490638814040889227238378510969934284150899244790369794594091320532) * 10 ^ 70 +
        7184197815494275435890863235193019915984743390337233067805795836525019) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (397 - x)) = _
  rw [show 398 = 207 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 26 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (398 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (398 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_398 :
    recurrence4Scalar1Left.coeff 398 =
      -((((9698189262958152242946129365052065770013878725871103078798 * 10 ^ 70 +
        0735709450118316242150415941435016352296927257940633388330122710906095) * 10 ^ 70 +
        2410527469200493932847479430898218317712074653768523576192763492501067) * 10 ^ 70 +
        7933052813161163384304320872882457009998217115114619829595426526288015) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (398 - x)) = _
  rw [show 399 = 208 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 25 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (399 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (399 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_399 :
    recurrence4Scalar1Left.coeff 399 =
      ((((3363000948392240711855007990001021931226596829920022450139 * 10 ^ 70 +
        8770254419649893239200538792303394791800210511164294207094331689056557) * 10 ^ 70 +
        1148887393247729445119288055183807771841084661582271649686966557815553) * 10 ^ 70 +
        3845697504918753783685128126406923297535687922970223986177812389646568) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (399 - x)) = _
  rw [show 400 = 209 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 24 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (400 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (400 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_400 :
    recurrence4Scalar1Left.coeff 400 =
      -((((1106162699042217673750501143396859749393183937962724373199 * 10 ^ 70 +
        6980409830882593221334563433959987330606650876951412561757954365823239) * 10 ^ 70 +
        0845542544506667950496252145360649549056863798192905226324350228800559) * 10 ^ 70 +
        3364303269046946626067447422949346615713495613175190604015473541103029) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (400 - x)) = _
  rw [show 401 = 210 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 23 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (401 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (401 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_401 :
    recurrence4Scalar1Left.coeff 401 =
      ((((342941454528929187117701649408725643606716506168835306203 * 10 ^ 70 +
        7621491378997060510060937471391692777377105646302477243007545896470175) * 10 ^ 70 +
        6141548473316803821434642884457392110685221355779128647736964202698479) * 10 ^ 70 +
        6965953500615753657654902979656828476565452515934401428789910073588996) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (401 - x)) = _
  rw [show 402 = 211 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 22 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (402 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (402 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_402 :
    recurrence4Scalar1Left.coeff 402 =
      -((((98917408296810271292170158808917936167325896172452075238 * 10 ^ 70 +
        9169418257578094511175341965660512776544462122859079807439191400257008) * 10 ^ 70 +
        5400387037596255149655546111624879898995381343463200222585982850039105) * 10 ^ 70 +
        4353881076843710411188718031963635799294629020482387471015307450565664) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (402 - x)) = _
  rw [show 403 = 212 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 21 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (403 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (403 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_403 :
    recurrence4Scalar1Left.coeff 403 =
      ((((25846881918653240098034177302852290182952481196438292163 * 10 ^ 70 +
        2570225796188144464798417345153265864641008668365226429169773339511799) * 10 ^ 70 +
        2154737625335994079643359869028001379978071241056494024315293872235177) * 10 ^ 70 +
        7131615875789113140133482786878238086467096229178946221832342698348831) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (403 - x)) = _
  rw [show 404 = 213 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 20 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (404 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (404 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_404 :
    recurrence4Scalar1Left.coeff 404 =
      -((((5740402188605195907472400344130340770211200135599075651 * 10 ^ 70 +
        0560003251999741123666681771231998711188719219727411244286395820992567) * 10 ^ 70 +
        2190573122789264921647764864345487586590772584428097401730498778034083) * 10 ^ 70 +
        9196843614328480620238869185752761695960025562418982160072582381567167) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (404 - x)) = _
  rw [show 405 = 214 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 19 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (405 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (405 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_405 :
    recurrence4Scalar1Left.coeff 405 =
      ((((862872694813203644206140148585639008528870726707884809 * 10 ^ 70 +
        8967064915181247241662684393189569207362875732855764767650662915568811) * 10 ^ 70 +
        3102163939232872677796778228325135324240118042485581256164447411617729) * 10 ^ 70 +
        9744257686529476786317350356872136002415883727270756313708784115368614) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (405 - x)) = _
  rw [show 406 = 215 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 18 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (406 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (406 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_406 :
    recurrence4Scalar1Left.coeff 406 =
      ((((64580528461842676327668427939213690958491912497404247 * 10 ^ 70 +
        5140426344799803355782779423849857514325572779137368147986789576850114) * 10 ^ 70 +
        2995395822250643736005192863973284563014217279761447828018657773962184) * 10 ^ 70 +
        5562824849090928545524406498265953089816634592560704181718331386290243) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (406 - x)) = _
  rw [show 407 = 216 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 17 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (407 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (407 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_407 :
    recurrence4Scalar1Left.coeff 407 =
      -((((129855082238557060531636140453726928486478398458326952 * 10 ^ 70 +
        0072211381698904914286665233272197993204202892821685277573499322148915) * 10 ^ 70 +
        9568046203136006468050496109477719390064035799037448565463452603325588) * 10 ^ 70 +
        6897678354882317782781371900463215928124531984314749904438120767317417) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (407 - x)) = _
  rw [show 408 = 217 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 16 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (408 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (408 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_408 :
    recurrence4Scalar1Left.coeff 408 =
      ((((73459474923106570375205302864195010801279789206854839 * 10 ^ 70 +
        6018836374486327695723341164531081636783691662559399068766588647134660) * 10 ^ 70 +
        7089682455127297177757354634919546782462683144628031349405279296747534) * 10 ^ 70 +
        1097128352039454060058962586724668040157171994372766447361314277541714) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (408 - x)) = _
  rw [show 409 = 218 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 15 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (409 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (409 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_409 :
    recurrence4Scalar1Left.coeff 409 =
      -((((31820808060979318536141641939563337208727640615542154 * 10 ^ 70 +
        4037147711301805069834593766475507552469801309177756450023727502243082) * 10 ^ 70 +
        6392356130604645363001636207816250350088262745977487867771263165615839) * 10 ^ 70 +
        3024993965341673086180955474982614459861939201039729347983884631501576) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (409 - x)) = _
  rw [show 410 = 219 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 14 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (410 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (410 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_410 :
    recurrence4Scalar1Left.coeff 410 =
      ((((11994358246079443290585941401826812595140920859566178 * 10 ^ 70 +
        9683890495452234652004104537769374887298675975130935985560637713488089) * 10 ^ 70 +
        2396486437086105963064866308802806266118950030216728262747177089172581) * 10 ^ 70 +
        3189819720392827392440320705534111116112038916802652886666450741164327) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (410 - x)) = _
  rw [show 411 = 220 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 13 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (411 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (411 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_411 :
    recurrence4Scalar1Left.coeff 411 =
      -((((4093671763381681896092051416408173094667996093033718 * 10 ^ 70 +
        5018460905050237008100748920873282186447989251926484817135527037917295) * 10 ^ 70 +
        7845514590531867474283596776966287501163374743623457848581552618040595) * 10 ^ 70 +
        4970592591284959260482848793370107295676550505828338598423548382496355) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (411 - x)) = _
  rw [show 412 = 221 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 12 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (412 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (412 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_412 :
    recurrence4Scalar1Left.coeff 412 =
      ((((1279919271796075695545371370259381360927466363969625 * 10 ^ 70 +
        9395963517978325275154296671380923570840430305438325485349175070209183) * 10 ^ 70 +
        0551724092038884498873180375015260763465414168392786190696355232625318) * 10 ^ 70 +
        9745357993942996022285614724118974824881865326959549056619899874358434) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (412 - x)) = _
  rw [show 413 = 222 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 11 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (413 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (413 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_413 :
    recurrence4Scalar1Left.coeff 413 =
      -((((364240652672719534656407688975153628253462084434102 * 10 ^ 70 +
        3419985171278512717081510964126738033519701850532104384619071642234280) * 10 ^ 70 +
        5484733120762020260584673016102477110082918827475485063668918854304877) * 10 ^ 70 +
        4107391998202213521235144502197855630197551440930291305605238757127339) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (413 - x)) = _
  rw [show 414 = 223 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 10 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (414 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (414 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_414 :
    recurrence4Scalar1Left.coeff 414 =
      ((((91321664644834798443420472916971665488340525665319 * 10 ^ 70 +
        6869021028907105602022973209332927536952039587201809480726558936793727) * 10 ^ 70 +
        7712521298751055130823100930486599751324285228301730376102860924059763) * 10 ^ 70 +
        7444773667273925475485147299406743971451332504838440215527581783518564) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (414 - x)) = _
  rw [show 415 = 224 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 9 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (415 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (415 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_415 :
    recurrence4Scalar1Left.coeff 415 =
      -((((18093747532835580094931853914879635823519590959047 * 10 ^ 70 +
        5299912497583999877128029133569553890273620795871722117037577042383698) * 10 ^ 70 +
        0943471285750363489270191334550555451627419500664566414032817088979510) * 10 ^ 70 +
        8342558641568778314270571948923146307134734783467450079207590644915365) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (415 - x)) = _
  rw [show 416 = 225 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 8 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (416 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (416 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_416 :
    recurrence4Scalar1Left.coeff 416 =
      ((((1406482427381880496917275668061640484620845854284 * 10 ^ 70 +
        3535156518383724821813346622282727829912979021605441814269171835531793) * 10 ^ 70 +
        3238688166584019888775097379902988964555717422853434906107629574176032) * 10 ^ 70 +
        4634937818662564289236177718066929197338073127047772509985006751798255) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (416 - x)) = _
  rw [show 417 = 226 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 7 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (417 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (417 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_417 :
    recurrence4Scalar1Left.coeff 417 =
      ((((1157762835744256948124674258530090550893825979758 * 10 ^ 70 +
        8544841375731930974319139188316223435000188492297111112828735019133558) * 10 ^ 70 +
        9737357803721534270173124970375218362946650720851294873397102512236948) * 10 ^ 70 +
        4840709909838745138023788703667819298184673173200706981795682795143364) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (417 - x)) = _
  rw [show 418 = 227 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 6 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (418 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (418 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_418 :
    recurrence4Scalar1Left.coeff 418 =
      -((((929318956110608539262677086872859490775358433728 * 10 ^ 70 +
        9223945280735823351859086278314892771964068651413934522587902823358253) * 10 ^ 70 +
        1620181821801449622014932646703778525066809965184897832096785347938424) * 10 ^ 70 +
        1149804731049418471702505947825838553536102874738345108587247150229125) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (418 - x)) = _
  rw [show 419 = 228 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 5 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (419 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (419 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_419 :
    recurrence4Scalar1Left.coeff 419 =
      ((((482532798387741048559158022224549802066621763098 * 10 ^ 70 +
        2018085154093259519784368587024677217731071925777641137935506559804199) * 10 ^ 70 +
        3656206730775272875848513862692501727630214597144877393921917775305030) * 10 ^ 70 +
        5652826316983765573641726104454260482430037230679419041903820912550965) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (419 - x)) = _
  rw [show 420 = 229 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 4 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (420 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (420 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_420 :
    recurrence4Scalar1Left.coeff 420 =
      -((((212802550572357516279276818998013942756872855859 * 10 ^ 70 +
        2952079727664940331509087990466261543387028886709537547051776657454939) * 10 ^ 70 +
        7045375904498403636574439865267542370522177742875207402955377624719073) * 10 ^ 70 +
        9928081166094371690554193953696438344467475339256811978058098127408297) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (420 - x)) = _
  rw [show 421 = 230 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 3 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (421 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (421 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_421 :
    recurrence4Scalar1Left.coeff 421 =
      ((((85485934851589261048121537841986589127367836226 * 10 ^ 70 +
        9226554947561281556844601239616532849331873963361472618191330679456930) * 10 ^ 70 +
        9218100292762478650690207657198514401693982352964041576581675256912819) * 10 ^ 70 +
        4784102538173421702272514605778261489462036194080591908961079321485280) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (421 - x)) = _
  rw [show 422 = 231 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 2 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (422 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (422 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_422 :
    recurrence4Scalar1Left.coeff 422 =
      -((((32162316501865814673465326214540829125997317131 * 10 ^ 70 +
        8634042671021146138533878564363120211999272491803526574007819747702961) * 10 ^ 70 +
        6116747266385140278723110149793709669615724471868184662133539799398663) * 10 ^ 70 +
        8683727173807980215388693580805732923079166274552759539602834003331337) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (422 - x)) = _
  rw [show 423 = 232 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 1 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (423 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (423 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_423 :
    recurrence4Scalar1Left.coeff 423 =
      ((((11481874743921516202302170479634166852776845910 * 10 ^ 70 +
        1178699175480294085065914435084039575835135000503029053277294987321254) * 10 ^ 70 +
        4189933263732237677157265446844914178947605976095126330153570848718749) * 10 ^ 70 +
        8783967675683629535835042393585389818222873933709738153407498383749465) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (423 - x)) = _
  rw [show 424 = 233 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (424 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (424 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_424 :
    recurrence4Scalar1Left.coeff 424 =
      -((((3914663403823228204292044633680909866561209145 * 10 ^ 70 +
        2553596080157661507293674855882181731270374611353986082432277846207611) * 10 ^ 70 +
        0570989106528106227676889898097985479741373582980236723717353619064150) * 10 ^ 70 +
        3307234237222509036469599899541951082468260058078817185812007994787358) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (424 - x)) = _
  rw [show 425 = 234 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 31 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (425 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (425 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_425 :
    recurrence4Scalar1Left.coeff 425 =
      ((((1278372127621498003456893497531497334324378763 * 10 ^ 70 +
        7254472650410482461200304417954883076615316805277582380453341455389521) * 10 ^ 70 +
        7408983869057327636061937179926488988616130997670717205879135223382317) * 10 ^ 70 +
        3587970728232440711378235027570001689297850861633746163600141222564702) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (425 - x)) = _
  rw [show 426 = 235 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 30 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (426 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (426 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_426 :
    recurrence4Scalar1Left.coeff 426 =
      -((((400138494182940937352050913189988885434639736 * 10 ^ 70 +
        1853398794330563085337823557533196348913385391847816349650964484640492) * 10 ^ 70 +
        1528367092207269982158212951890885267165101609785591666140434787470789) * 10 ^ 70 +
        7024479079480385853113208085110714368745852738581162702958886747847140) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (426 - x)) = _
  rw [show 427 = 236 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 29 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (427 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (427 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_427 :
    recurrence4Scalar1Left.coeff 427 =
      ((((119940980908781630738642118102236482338902050 * 10 ^ 70 +
        8890216630082286208472907960888265853441568916346970514436367263124963) * 10 ^ 70 +
        4460750965310800469262487976404614402625908939104451034324071596917706) * 10 ^ 70 +
        8727569997354984061315842353983231586068922582460384195688022784416831) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (427 - x)) = _
  rw [show 428 = 237 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 28 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (428 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (428 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_428 :
    recurrence4Scalar1Left.coeff 428 =
      -((((34351022770405895073747739370294362769411508 * 10 ^ 70 +
        4374188178199811427915305710788107246800107404607045601180426861876626) * 10 ^ 70 +
        1376514069340982981055174330266265752288598989583022014969455616497616) * 10 ^ 70 +
        6409779029984476582629676320172191529972275747980985518367745631942092) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (428 - x)) = _
  rw [show 429 = 238 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 27 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (429 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (429 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_429 :
    recurrence4Scalar1Left.coeff 429 =
      ((((9364791229593532654498093461439607572729027 * 10 ^ 70 +
        6868762667807965265114908665981535099723499335909312905285422822523813) * 10 ^ 70 +
        4427868198305468905275554554505650839721088245013809336688065813576987) * 10 ^ 70 +
        9789963339841472929609490025062195356618584410563259591262834505255979) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (429 - x)) = _
  rw [show 430 = 239 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 26 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (430 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (430 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_430 :
    recurrence4Scalar1Left.coeff 430 =
      -((((2416517058413532419522045410121438329690419 * 10 ^ 70 +
        6950151354591925335708797769088109566470024268006832588939446934629435) * 10 ^ 70 +
        7251501295623898421678881480524985936476631051178438329912985595715340) * 10 ^ 70 +
        2260238852221603424171678040052523849767906450824196549772014365285000) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (430 - x)) = _
  rw [show 431 = 240 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 25 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (431 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (431 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_431 :
    recurrence4Scalar1Left.coeff 431 =
      ((((585186031871402949084197602869897892549236 * 10 ^ 70 +
        4187205467842634781552288613858706995969088545756514975289555875488553) * 10 ^ 70 +
        0238072896392935881378905369169431075732398712244206456041480437329425) * 10 ^ 70 +
        0310647063532655022298118861114165404967056350021961887972866210532136) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (431 - x)) = _
  rw [show 432 = 241 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 24 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (432 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (432 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_432 :
    recurrence4Scalar1Left.coeff 432 =
      -((((131163035105970972927118783289432202836975 * 10 ^ 70 +
        0768292582251485305520134060046627506761475249195675293111658513865739) * 10 ^ 70 +
        3281936884809685881278586370674751057083516411663747804469735505061759) * 10 ^ 70 +
        8126238839529301016707848067611651145314239297951988147387170884785349) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (432 - x)) = _
  rw [show 433 = 242 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 23 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (433 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (433 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_433 :
    recurrence4Scalar1Left.coeff 433 =
      ((((26541825684737495493584632331449969352521 * 10 ^ 70 +
        7797466548063247032690226420901744109048266069683583690935475963627454) * 10 ^ 70 +
        8563167498789621236862344146501447023869214768374318497013692676598830) * 10 ^ 70 +
        8794842572458934870740477037975555976056576741563166169796750746842913) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (433 - x)) = _
  rw [show 434 = 243 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 22 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (434 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (434 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_434 :
    recurrence4Scalar1Left.coeff 434 =
      -((((4593978303895164349835397541317397777853 * 10 ^ 70 +
        8357585542620204578037859878619661845588390862644857715329842493776356) * 10 ^ 70 +
        0597969699551645323890646661060730923084885564975895934679440225746195) * 10 ^ 70 +
        9924767537406149961517425209998014850156562935165831283147143003128797) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (434 - x)) = _
  rw [show 435 = 244 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 21 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (435 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (435 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_435 :
    recurrence4Scalar1Left.coeff 435 =
      ((((575288254544630280855509623318509996491 * 10 ^ 70 +
        4540821772627717670795863369963260350483109897036496303824213876792637) * 10 ^ 70 +
        3717476024988596684170748660995684927226030873400477694237838071244967) * 10 ^ 70 +
        2051783186521114032938961483927679327254299863706884145383699644378839) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (435 - x)) = _
  rw [show 436 = 245 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 20 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (436 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (436 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_436 :
    recurrence4Scalar1Left.coeff 436 =
      -((((2406559325887635573976435306216163283 * 10 ^ 70 +
        2976019331522191990564579827172209182782986821886897956775147432895018) * 10 ^ 70 +
        5898083038292596990585947408815320620266083710242577751904539654470288) * 10 ^ 70 +
        3826929706328748471500467693503698171101849546038854721920000305718210) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (436 - x)) = _
  rw [show 437 = 246 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 19 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (437 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (437 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_437 :
    recurrence4Scalar1Left.coeff 437 =
      -((((29891023358847911112426875739660812825 * 10 ^ 70 +
        9828259489373685924898081561027240863969630166955611135850796851103545) * 10 ^ 70 +
        1959076746148176260822496857886306475887768550396800112533432285107055) * 10 ^ 70 +
        5720293272877339198688092613064390395386438254709432824453600590500281) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (437 - x)) = _
  rw [show 438 = 247 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 18 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (438 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (438 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_438 :
    recurrence4Scalar1Left.coeff 438 =
      ((((13010723756247418035432382494027662855 * 10 ^ 70 +
        9193215965654204929154646531268427305174469378894309238969959677882244) * 10 ^ 70 +
        2876970585989050553885198726751359430801200663409288147682951401646612) * 10 ^ 70 +
        1435876707034669867494243095253956236877819169307894373584002140215484) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (438 - x)) = _
  rw [show 439 = 248 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 17 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (439 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (439 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_439 :
    recurrence4Scalar1Left.coeff 439 =
      -((((3999259113682983848637265077111126538 * 10 ^ 70 +
        6634271624850323117718166583727770465049307100196608531630975603221126) * 10 ^ 70 +
        9609067213400356674041476581879958872010700896676083144278882208378101) * 10 ^ 70 +
        2995104924458215575702435781848648215544434446116273509173458368347658) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (439 - x)) = _
  rw [show 440 = 249 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 16 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (440 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (440 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_440 :
    recurrence4Scalar1Left.coeff 440 =
      ((((1027776035935295289305202520241402198 * 10 ^ 70 +
        2679018086250402984089797767152089737752209213715798063299284811161896) * 10 ^ 70 +
        2479636761586342909405501148972995312587172517924103281538371150343183) * 10 ^ 70 +
        5897333499983847992188625989840277619771284997759578698220429792225342) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (440 - x)) = _
  rw [show 441 = 250 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 15 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (441 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (441 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_441 :
    recurrence4Scalar1Left.coeff 441 =
      -((((231251955665703494424127447852119401 * 10 ^ 70 +
        2598798477410450065880239429692645817463801558533053931143018179042989) * 10 ^ 70 +
        5662204175146855020261997540951458890295004099554480681519361572327925) * 10 ^ 70 +
        5614126200980004316532485661219263162009995421619272700245456745865525) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (441 - x)) = _
  rw [show 442 = 251 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 14 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (442 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (442 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_442 :
    recurrence4Scalar1Left.coeff 442 =
      ((((46089577964888753620824143203213506 * 10 ^ 70 +
        1333381719882837912361004383252310444481028244241009777051261550142978) * 10 ^ 70 +
        1827747500130191884977296434296939203624278867224148620369823257523660) * 10 ^ 70 +
        7091965099947498100460374712361579745385574632637295944164022914198084) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (442 - x)) = _
  rw [show 443 = 252 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 13 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (443 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (443 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_443 :
    recurrence4Scalar1Left.coeff 443 =
      -((((8069300072765237991634966161364396 * 10 ^ 70 +
        1571931959425119684514965528379489208786084342521626840216655378935733) * 10 ^ 70 +
        8837249938930985916557972301709995828981557835189680602900626767744420) * 10 ^ 70 +
        9895502551016451744095964678524709643345406252642647694096094790445251) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (443 - x)) = _
  rw [show 444 = 253 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 12 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (444 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (444 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_444 :
    recurrence4Scalar1Left.coeff 444 =
      ((((1198806180865512505756706882022276 * 10 ^ 70 +
        5758193380011465742955448850266079229063562792274480674487293232477950) * 10 ^ 70 +
        0798344579693390247222736867230892667751702526938312608245336940313830) * 10 ^ 70 +
        8046506470824311610437148643960338800648964869598637842283605062891089) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (444 - x)) = _
  rw [show 445 = 254 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 11 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (445 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (445 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_445 :
    recurrence4Scalar1Left.coeff 445 =
      -((((135774033617972453249119564295596 * 10 ^ 70 +
        1466261182890042171005036925024351497754707920620530987980570023396298) * 10 ^ 70 +
        4002531216111101679121313243218563985547443043228260365748560240250423) * 10 ^ 70 +
        7327214549820489201658828267609200698308219982425645887603567782615546) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (445 - x)) = _
  rw [show 446 = 255 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 10 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (446 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (446 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_446 :
    recurrence4Scalar1Left.coeff 446 =
      ((((6264856624738396492816184038998 * 10 ^ 70 +
        7116339014331423450764570981878949565114939258790417699740327067790836) * 10 ^ 70 +
        2848577205897829758733419763315590430453018723620684660344785583920570) * 10 ^ 70 +
        1186427690869546056616748829308827461927124732850049462512621684192383) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (446 - x)) = _
  rw [show 447 = 256 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 9 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (447 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (447 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_447 :
    recurrence4Scalar1Left.coeff 447 =
      ((((2168847829129852421249351533330 * 10 ^ 70 +
        2628213230922194126986713573804765305205008694066594460192135869991928) * 10 ^ 70 +
        0551409298171743697379957092526892277533443710445440511246486180810086) * 10 ^ 70 +
        1424300288082015293004309432343704965229297045301029507675321172564361) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (447 - x)) = _
  rw [show 448 = 257 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 8 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (448 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (448 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_448 :
    recurrence4Scalar1Left.coeff 448 =
      -((((862558149006449178001691791492 * 10 ^ 70 +
        3030647608276692232194154540297025299878180360424529848537297539681815) * 10 ^ 70 +
        3708372004881773688846705884208165403876812138662307294619501407596078) * 10 ^ 70 +
        7664480466203794249962927370742237977994866776442882121845558542670715) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (448 - x)) = _
  rw [show 449 = 258 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 7 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (449 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (449 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_449 :
    recurrence4Scalar1Left.coeff 449 =
      ((((201169561634252249444304747596 * 10 ^ 70 +
        9858610219413276727505878479891585767906996904924821436181860778431331) * 10 ^ 70 +
        1371766178122496132476095831111477072679890669060649609327336285707775) * 10 ^ 70 +
        4707201222632426342740386040328792445396582252708914406070280356554938) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (449 - x)) = _
  rw [show 450 = 259 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 6 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (450 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (450 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_450 :
    recurrence4Scalar1Left.coeff 450 =
      -((((36270259122213027093287891910 * 10 ^ 70 +
        5099461567971986122084153643231040357906453194638674416101038681555152) * 10 ^ 70 +
        6972734916447260324390228657583014265944510250160713053944985707163761) * 10 ^ 70 +
        7264754131501200195626662550563504559729822701337443767702117893868536) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (450 - x)) = _
  rw [show 451 = 260 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 5 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (451 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (451 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_451 :
    recurrence4Scalar1Left.coeff 451 =
      ((((5258511461689442433193255130 * 10 ^ 70 +
        4938707563294342199373822935348432437910597250563740418751045257234992) * 10 ^ 70 +
        3120878370398263663120626734466940113723668940994631514584097144092606) * 10 ^ 70 +
        8109606378144519143204326882004177031912845753791352620808094030092622) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (451 - x)) = _
  rw [show 452 = 261 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 4 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (452 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (452 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_452 :
    recurrence4Scalar1Left.coeff 452 =
      -((((580282066559575459161344030 * 10 ^ 70 +
        3076950758328795301087538032897452004402321844134715605053444099189692) * 10 ^ 70 +
        1314372035991743862599549459487607665197638137054802292797190041863437) * 10 ^ 70 +
        9469789845113949964044164753725526335276296659398178456940872455642789) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (452 - x)) = _
  rw [show 453 = 262 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 3 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (453 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (453 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_453 :
    recurrence4Scalar1Left.coeff 453 =
      ((((34592045473925155235507196 * 10 ^ 70 +
        3695360671561518951514543636347079521866580944442002124281869526613380) * 10 ^ 70 +
        9553350391282264482735588236625643099583557822419894390146699101095855) * 10 ^ 70 +
        8544791141700716902143599715481459584987260098598870669753969160564959) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (453 - x)) = _
  rw [show 454 = 263 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 2 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (454 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (454 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_454 :
    recurrence4Scalar1Left.coeff 454 =
      ((((3845651136587842613613737 * 10 ^ 70 +
        4930117416045920310304294707465383985956216445379912334907535578871225) * 10 ^ 70 +
        2484991391786343082148911985033308493034642955809918531668539598406223) * 10 ^ 70 +
        3186147935651560405535612469256558569494705463305849198662900327979201) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (454 - x)) = _
  rw [show 455 = 264 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 1 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (455 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (455 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_455 :
    recurrence4Scalar1Left.coeff 455 =
      -((((1738553356528068496672075 * 10 ^ 70 +
        8953654138767086871025392273182320396897955648259162552670058991555918) * 10 ^ 70 +
        8020990283998539400861393921467202075539568671829545211293139844247150) * 10 ^ 70 +
        0288003293688427785868488546297314720240190527067577775550718278652636) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (455 - x)) = _
  rw [show 456 = 265 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (456 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (456 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_456 :
    recurrence4Scalar1Left.coeff 456 =
      ((((361008070025396828870342 * 10 ^ 70 +
        1923186620408246227782402366867054058480000434381237705334902981402055) * 10 ^ 70 +
        9798589705854979569800089432950808845231196325347814416730864458101349) * 10 ^ 70 +
        7807103266469749203388420353722132981865470309621177408427013707209802) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (456 - x)) = _
  rw [show 457 = 266 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 31 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (457 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (457 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_457 :
    recurrence4Scalar1Left.coeff 457 =
      -((((55352188312254095683393 * 10 ^ 70 +
        5390323807546164406437273520771819930825587288638047638331362727794253) * 10 ^ 70 +
        9684609695716732956660986320798207786883398205810866976568140775772907) * 10 ^ 70 +
        8756074595373323899768013627408331494315592487654636081688234531631588) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (457 - x)) = _
  rw [show 458 = 267 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 30 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (458 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (458 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_458 :
    recurrence4Scalar1Left.coeff 458 =
      ((((6712601533956668006024 * 10 ^ 70 +
        7572187715126244630590239582891710499431048933409955002133841376797369) * 10 ^ 70 +
        7633091833148513466591655641222697667832747453614322494523058699224088) * 10 ^ 70 +
        7914789649129932440119756131153549277372045755751248671172155559617387) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (458 - x)) = _
  rw [show 459 = 268 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 29 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (459 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (459 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_459 :
    recurrence4Scalar1Left.coeff 459 =
      -((((625889639461695880140 * 10 ^ 70 +
        3987906781513308361114555025447384632922178160725097798441443570137453) * 10 ^ 70 +
        3621386216805013442820963230765220096239139201893441625212690229061077) * 10 ^ 70 +
        6698680395662015634319580944186414133227752098972700062909537513970277) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (459 - x)) = _
  rw [show 460 = 269 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 28 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (460 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (460 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_460 :
    recurrence4Scalar1Left.coeff 460 =
      ((((36643011326413138023 * 10 ^ 70 +
        5592962290670860924141590631061465196237347010846722679471851182760450) * 10 ^ 70 +
        5833110017276881603212006902576492894195342264715817198542886242680231) * 10 ^ 70 +
        2151546670390573637337544819148932269626906693762203031247655490729805) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (460 - x)) = _
  rw [show 461 = 270 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 27 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (461 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (461 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_461 :
    recurrence4Scalar1Left.coeff 461 =
      ((((764940579819563599 * 10 ^ 70 +
        3695810980997061798709280621677317018767203565419247335184271138589057) * 10 ^ 70 +
        4462518395618113380670156349686767156539324268421859254121526684776163) * 10 ^ 70 +
        5319498307149880814321438696881631078719638470715393864071494758626737) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (461 - x)) = _
  rw [show 462 = 271 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 26 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (462 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (462 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_462 :
    recurrence4Scalar1Left.coeff 462 =
      -((((579199239080349853 * 10 ^ 70 +
        8134501324910455518585568837497389846905836341071564658477833346658699) * 10 ^ 70 +
        0062476085831115900425214348769249998874191608105818810382229589749134) * 10 ^ 70 +
        7129887061567913912678663412842392881999015288604683187996221082949438) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (462 - x)) = _
  rw [show 463 = 272 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 25 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (463 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (463 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_463 :
    recurrence4Scalar1Left.coeff 463 =
      ((((96676425119551403 * 10 ^ 70 +
        7279353885778252596460270655491073772726872576133033581309373091147191) * 10 ^ 70 +
        1905468025288711720339499471041905985289933334006303594106381923951971) * 10 ^ 70 +
        1422941558688679085226338634369104693251721685296185388744179936007106) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (463 - x)) = _
  rw [show 464 = 273 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 24 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (464 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (464 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_464 :
    recurrence4Scalar1Left.coeff 464 =
      -((((10958994546961608 * 10 ^ 70 +
        3173114104953286491910721621874633173771956985024537168960593852351525) * 10 ^ 70 +
        0152921984190943020687584847976455296536282880229863061974566488123900) * 10 ^ 70 +
        4011588223572785023788592342198350415083536128044578432868512043797843) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (464 - x)) = _
  rw [show 465 = 274 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 23 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (465 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (465 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_465 :
    recurrence4Scalar1Left.coeff 465 =
      ((((932426734005659 * 10 ^ 70 +
        5591969963864007772162660371271079294892944528840233068937828886789171) * 10 ^ 70 +
        9874839584809982312121148431315518748149750446948354971144202107161751) * 10 ^ 70 +
        6956515781058095102615185584076278163187959145824717079459345910532488) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (465 - x)) = _
  rw [show 466 = 275 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 22 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (466 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (466 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_466 :
    recurrence4Scalar1Left.coeff 466 =
      -((((57093736000892 * 10 ^ 70 +
        3391918479561655682446524586808102703795379548149459198384815133641669) * 10 ^ 70 +
        8674397953359199605530077805259928715291720873834238911641620661849567) * 10 ^ 70 +
        7673245829531686445943376282683800168633515425589561632635846598231405) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (466 - x)) = _
  rw [show 467 = 276 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 21 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (467 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (467 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_467 :
    recurrence4Scalar1Left.coeff 467 =
      ((((1791758970128 * 10 ^ 70 +
        6524135762994076178919284282333155004947154090007745233440666402058024) * 10 ^ 70 +
        2997437928139387162130030704438034140588204979857050758246470169783859) * 10 ^ 70 +
        0389831503809893009339229712169078523792359752700763274755846367245402) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (467 - x)) = _
  rw [show 468 = 277 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 20 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (468 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (468 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_468 :
    recurrence4Scalar1Left.coeff 468 =
      ((((96744924685 * 10 ^ 70 +
        8950800624355732191876315152913840410157874192875479246370899885637774) * 10 ^ 70 +
        2188092411526480820772727226990579215273370784941534572148156241036464) * 10 ^ 70 +
        4004132296034629592675300469486500618010206241723279484065387281394626) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (468 - x)) = _
  rw [show 469 = 278 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 19 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (469 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (469 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_469 :
    recurrence4Scalar1Left.coeff 469 =
      -((((20192779012 * 10 ^ 70 +
        8006261237428443349826656715123845116494254649262712240056695088365090) * 10 ^ 70 +
        7712417329168648126407238622153610687515978763277024494777076707384011) * 10 ^ 70 +
        7016417403576776882706281775777116294763077973464742241107597396481534) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (469 - x)) = _
  rw [show 470 = 279 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 18 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_469_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (470 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (470 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_470 :
    recurrence4Scalar1Left.coeff 470 =
      ((((1753503353 * 10 ^ 70 +
        2071563914855739259870277169263017100542934519936047310929929148547568) * 10 ^ 70 +
        4316890997486695338945185613104879380238835002085109644790494134865997) * 10 ^ 70 +
        9854055080677074988079433126340867034465329237240430722039351425862317) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (470 - x)) = _
  rw [show 471 = 280 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 17 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_470_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (471 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (471 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_471 :
    recurrence4Scalar1Left.coeff 471 =
      -((((97543166 * 10 ^ 70 +
        7992993617217869783493159501653018226287629558584517728933234438717880) * 10 ^ 70 +
        5463230935761525850234117419454913192139826173443317761262899027299803) * 10 ^ 70 +
        2633980542653822262908095301057881542246938442596222523924573089934097) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (471 - x)) = _
  rw [show 472 = 281 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 16 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_471_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (472 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (472 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_472 :
    recurrence4Scalar1Left.coeff 472 =
      ((((3200232 * 10 ^ 70 +
        1588125224219900667323844221797311108443608265518289931068239875942542) * 10 ^ 70 +
        1903919412525423493158092099931606962235652963515017469771383320123159) * 10 ^ 70 +
        6478537111021959871554131982174665204360782619291987373828942780460439) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (472 - x)) = _
  rw [show 473 = 282 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 15 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_472_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (473 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (473 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_473 :
    recurrence4Scalar1Left.coeff 473 =
      -((((3327 * 10 ^ 70 +
        3765590571490417730488630997335292118277097602400781221196544563374887) * 10 ^ 70 +
        6262207203587112635042370678932866539668546715871116188615046084223219) * 10 ^ 70 +
        3910259799730722855294630724000486058753944316209946277564332425569679) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (473 - x)) = _
  rw [show 474 = 283 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 14 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_473_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (474 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (474 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_474 :
    recurrence4Scalar1Left.coeff 474 =
      -((((6290 * 10 ^ 70 +
        7230899356039570431412266758946535503317641499859695808748006142201503) * 10 ^ 70 +
        0059680085521737490479622354172819882739851416086231632476448866979802) * 10 ^ 70 +
        4107834892326327633708085803870863451505308872794660542194507419913340) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (474 - x)) = _
  rw [show 475 = 284 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 13 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_474_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (475 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (475 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_475 :
    recurrence4Scalar1Left.coeff 475 =
      ((((368 * 10 ^ 70 +
        5289244090458035008348362618670113971723910379885624400361034840992301) * 10 ^ 70 +
        5259348613277201609262447876908536815618418233681488325156736113680747) * 10 ^ 70 +
        7011815605408240818192770558731553643084861772527839350941467532217880) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (475 - x)) = _
  rw [show 476 = 285 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 12 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_475_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (476 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (476 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_476 :
    recurrence4Scalar1Left.coeff 476 =
      -((((9 * 10 ^ 70 +
        6622412207518455231328401519123023538094552841445692801925062845823236) * 10 ^ 70 +
        3552729097972625488714934991004135963685633627322537469363865762981833) * 10 ^ 70 +
        9301687788913165446970263336764157042723537355299591418208105005690527) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (476 - x)) = _
  rw [show 477 = 286 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 11 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_476_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (477 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (477 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_477 :
    recurrence4Scalar1Left.coeff 477 =
      (((46500728879889980041563090278680000545103611328997646452230962750340 * 10 ^ 70 +
        8839303794179839891848005340547941904979384359072235534642459600450523) * 10 ^ 70 +
        6848728735128420733458432937424400701070447551094801604664198874262915) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (477 - x)) = _
  rw [show 478 = 287 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 10 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_477_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
