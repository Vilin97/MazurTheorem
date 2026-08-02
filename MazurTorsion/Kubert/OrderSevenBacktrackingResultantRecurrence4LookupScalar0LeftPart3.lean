/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar0Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (371 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (371 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_371 :
    recurrence4Scalar0Left.coeff 371 =
      -(((((122 * 10 ^ 70 +
        0118824204385462454323303045314574394284362355770711329188408541932742) * 10 ^ 70 +
        3792785004859641550747940278107981165725797731009452517912227500344454) * 10 ^ 70 +
        0110628549406951012800219409566674438105760898557754549858224222356764) * 10 ^ 70 +
        5096463827104715770436943680070390886342860097226038687760915177687382) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (371 - x)) = _
  rw [show 372 = 177 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 24 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (372 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (372 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_372 :
    recurrence4Scalar0Left.coeff 372 =
      (((((48 * 10 ^ 70 +
        5126123407714167374042720378484902235396005684779152597395742983828752) * 10 ^ 70 +
        2067713920547931346971356120665297437459997828724168867895774706792238) * 10 ^ 70 +
        9063994915124001273217583340882233135186498740818160641410844089595358) * 10 ^ 70 +
        0406741003313996576547860698662961939352204717620585575628772164308258) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (372 - x)) = _
  rw [show 373 = 178 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 23 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (373 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (373 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_373 :
    recurrence4Scalar0Left.coeff 373 =
      -(((((18 * 10 ^ 70 +
        6787756963247983858121527122948666265807317369976834096809060911759573) * 10 ^ 70 +
        3302573153762494085079208444926294318386874058857184276326706361280836) * 10 ^ 70 +
        3241984274280414460837524257520353788534410285909730262131952173335944) * 10 ^ 70 +
        4660079791910318930183464688403136329886105307641076491391622483816594) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (373 - x)) = _
  rw [show 374 = 179 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 22 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (374 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (374 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_374 :
    recurrence4Scalar0Left.coeff 374 =
      (((((6 * 10 ^ 70 +
        9429314539554788326875262111749756932902727702055785604599891554458081) * 10 ^ 70 +
        0322297789904322061879863394571288994360616274152898775565800717826042) * 10 ^ 70 +
        5113252636448823376955757874469074886233367531208718609748940213048217) * 10 ^ 70 +
        5279971673322581409447614925714552254355916111775412569825341215697746) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (374 - x)) = _
  rw [show 375 = 180 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 21 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (375 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (375 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_375 :
    recurrence4Scalar0Left.coeff 375 =
      -(((((2 * 10 ^ 70 +
        4815951965071962432928311218383081925525113413390935928806863500203245) * 10 ^ 70 +
        7705720345695958864232285404797416080339443591871608568027837265933954) * 10 ^ 70 +
        1234903155308952234173532204836830471137726681030477614492286362850481) * 10 ^ 70 +
        9904890812861804156324211209761019710441087302137813697955894146540514) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (375 - x)) = _
  rw [show 376 = 181 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 20 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (376 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (376 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_376 :
    recurrence4Scalar0Left.coeff 376 =
      ((((8482052563145206837427464394419752886627822726305469917937549033546969 * 10 ^ 70 +
        5573237571283508981091159761902947941085902894798771325924852205861180) * 10 ^ 70 +
        1491757454694109820746892849367914194504580370931209721119147422214652) * 10 ^ 70 +
        6267319468441159644537581422953603822568540435429962453308546530403712) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (376 - x)) = _
  rw [show 377 = 182 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 19 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (377 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (377 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_377 :
    recurrence4Scalar0Left.coeff 377 =
      -((((2748843892165293502178818882915317910671010890518427401668382723296379 * 10 ^ 70 +
        9909031710922119812824712821927538519509918935966041913295582672631869) * 10 ^ 70 +
        0295954699462009221494646284581829170373039775370135739769630358664465) * 10 ^ 70 +
        6122175157261922736628966209287326213896070133522883441561053651189106) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (377 - x)) = _
  rw [show 378 = 183 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 18 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (378 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (378 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_378 :
    recurrence4Scalar0Left.coeff 378 =
      ((((832649828209127436800992679030595372241683021458358714283152207843221 * 10 ^ 70 +
        9738187652418044174471047658119893082196040830969099335632727416453902) * 10 ^ 70 +
        9007456246913411921772950484672961500931680839668050933443270071921294) * 10 ^ 70 +
        5694662582141280078476041987725845530279239152458886831129815991220053) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (378 - x)) = _
  rw [show 379 = 184 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 17 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (379 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (379 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_379 :
    recurrence4Scalar0Left.coeff 379 =
      -((((229431302412950839586087537325795471679259301335809454265111855867864 * 10 ^ 70 +
        7669522399527606502636298986134148157382998655787968564338733277164806) * 10 ^ 70 +
        3775552670899327913315940563242089486096751369480003544219955085797031) * 10 ^ 70 +
        5558549586830394938642636409056615864363678876670216426253317889344375) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (379 - x)) = _
  rw [show 380 = 185 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 16 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (380 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (380 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_380 :
    recurrence4Scalar0Left.coeff 380 =
      ((((54013140557207636161758865843627521375217118180041748639649300590769 * 10 ^ 70 +
        4527286537501885004524365808029150057317758020022697407261685617319826) * 10 ^ 70 +
        4690195604728168089285900934461500308248207143783048998661610055549332) * 10 ^ 70 +
        4218314289032358115196409483212135021419433422797466059812069423463190) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (380 - x)) = _
  rw [show 381 = 186 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 15 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (381 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (381 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_381 :
    recurrence4Scalar0Left.coeff 381 =
      -((((8744374782623523506741775305105730141232137367283210389200102984840 * 10 ^ 70 +
        7657920915574227361187807421787907179237381117535234870555159881580620) * 10 ^ 70 +
        1425671735414826410312114268068950069423971849157894459446973807742966) * 10 ^ 70 +
        9100514397421941353777436041130720926646666028605163205180876565573710) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (381 - x)) = _
  rw [show 382 = 187 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 14 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (382 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (382 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_382 :
    recurrence4Scalar0Left.coeff 382 =
      -((((551160866337916558319939119908384785032317325767727564815979971587 * 10 ^ 70 +
        7750032027245259566282262038764606476360646037744599566433450862096530) * 10 ^ 70 +
        7642182019431231961224408811518767667268345796392162758796758433616206) * 10 ^ 70 +
        4555391736972568047864620145803969455148794058546366042655724216201895) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (382 - x)) = _
  rw [show 383 = 188 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 13 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (383 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (383 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_383 :
    recurrence4Scalar0Left.coeff 383 =
      ((((1369283993103281129270831906280663148828498081979292732711694319413 * 10 ^ 70 +
        7815408736888767991082700426175398466532619890999437237843338293999518) * 10 ^ 70 +
        6647142552660305347807857072373679826492895147266490211834237764818513) * 10 ^ 70 +
        5784481786200974567710862053888341905955137827356250704896591001829173) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (383 - x)) = _
  rw [show 384 = 189 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 12 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_383_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (384 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (384 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_384 :
    recurrence4Scalar0Left.coeff 384 =
      -((((823618415700844231237052874904785952707566421929671288460183611734 * 10 ^ 70 +
        0105837533148777752222779844038088075152362837033409114852347006053084) * 10 ^ 70 +
        0186182411352934705229532201013559409407667412706292850535225152107021) * 10 ^ 70 +
        1456385360347938259633729233060658254066369521296097049089043257401969) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (384 - x)) = _
  rw [show 385 = 190 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 11 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_384_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (385 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (385 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_385 :
    recurrence4Scalar0Left.coeff 385 =
      ((((374110078091025236046412498332448165776935016142532591909386820502 * 10 ^ 70 +
        9559746349317852142910715500136655749757193991504128671056556126889535) * 10 ^ 70 +
        0549286966784513523154616151572303541080340434136196102270117660669438) * 10 ^ 70 +
        0689859671533619563535333868406364403138694178086587824056338502815903) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (385 - x)) = _
  rw [show 386 = 191 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 10 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_385_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (386 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (386 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_386 :
    recurrence4Scalar0Left.coeff 386 =
      -((((145987096140794536344188885315711947417048313582541945845573036414 * 10 ^ 70 +
        7219960987613114524276708948542077650111456813943670497617272903606149) * 10 ^ 70 +
        2803798557040134285821803022386343152950928591448899303158961753840892) * 10 ^ 70 +
        0577995604958588512565000069790393702110391733316805967418575549212810) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (386 - x)) = _
  rw [show 387 = 192 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 9 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_386_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (387 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (387 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_387 :
    recurrence4Scalar0Left.coeff 387 =
      ((((50577001848206574153614216982292977130292385056011740866509864323 * 10 ^ 70 +
        3673851980955268064377424044856021134510156854913066208454633470901659) * 10 ^ 70 +
        0296948071492189851335395452451480587526874892675385900749513166340216) * 10 ^ 70 +
        9537833169267915111258860908204981609046448952289454538071453266290921) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (387 - x)) = _
  rw [show 388 = 193 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 8 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_387_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (388 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (388 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_388 :
    recurrence4Scalar0Left.coeff 388 =
      -((((15484340094311253466751526834409767424328010384099522298702377073 * 10 ^ 70 +
        8965595094835345433379282926309639099201755642737100204118264204560311) * 10 ^ 70 +
        4081762601563768662251281315338252327326970481818812010312922007166304) * 10 ^ 70 +
        5490631100080979870535111976130747475791971927746507919197938702854243) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (388 - x)) = _
  rw [show 389 = 194 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 7 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_388_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (389 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (389 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_389 :
    recurrence4Scalar0Left.coeff 389 =
      ((((3985957966118727127405307211553739404703999716738695558841813298 * 10 ^ 70 +
        4560467386006304863032531749383867110740226499413164467519862939944835) * 10 ^ 70 +
        4424560283283184105591303363473971003241441353999903528202258103264145) * 10 ^ 70 +
        3143247237601669002636107208909472896875010020551627228147975018060646) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (389 - x)) = _
  rw [show 390 = 195 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 6 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_389_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (390 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (390 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_390 :
    recurrence4Scalar0Left.coeff 390 =
      -((((700112474485490022609470676227467384615482754450312960103087157 * 10 ^ 70 +
        9760032966042803709383150029641678574879792299821599112500706903136845) * 10 ^ 70 +
        8608030466390281378755756892407481055661259414198511519963053763312126) * 10 ^ 70 +
        9747687844694601368264058522435875435066619474813921476204432201616952) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (390 - x)) = _
  rw [show 391 = 196 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 5 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_390_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (391 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (391 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_391 :
    recurrence4Scalar0Left.coeff 391 =
      -((((48426913984079391502517424743280912230359316356965307352723379 * 10 ^ 70 +
        7694896403585542315270400492686749029196061617344003850593695159313377) * 10 ^ 70 +
        8960963941772792377946290559985679443284923212154383539260265547895261) * 10 ^ 70 +
        5545473436583930940996573681846416384547450927032243386241975203162647) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (391 - x)) = _
  rw [show 392 = 197 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 4 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_391_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (392 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (392 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_392 :
    recurrence4Scalar0Left.coeff 392 =
      ((((130210966969827654556739938498901857258953404770173348959922631 * 10 ^ 70 +
        7851996835753695416821005432108102493872451957356000501404729902528126) * 10 ^ 70 +
        9945939354510565103784373881424082723810371381268929934507617008260658) * 10 ^ 70 +
        7699292883758940835980160484933569943602314064620460715786837516327774) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (392 - x)) = _
  rw [show 393 = 198 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 3 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_392_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (393 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (393 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_393 :
    recurrence4Scalar0Left.coeff 393 =
      -((((86326821978015692101790067102978554631104801630888706039957768 * 10 ^ 70 +
        8933636042830235197131805030537600866887265286025549186111239058824354) * 10 ^ 70 +
        4827087243613697503861542475982406922373163568187429420092200416953708) * 10 ^ 70 +
        0224527702022491891868135521742673280211432370991804714244977153612672) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (393 - x)) = _
  rw [show 394 = 199 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 2 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_393_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (394 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (394 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_394 :
    recurrence4Scalar0Left.coeff 394 =
      ((((43982076148679491018658408521865738167413625899525649262513641 * 10 ^ 70 +
        2982703374291418992981898298915703229856338472102245149499970983126274) * 10 ^ 70 +
        4705670927219170061363099206243869537452506905578093355967961963962617) * 10 ^ 70 +
        1748106982153931314637716531240048289220829020957002245515540873554873) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (394 - x)) = _
  rw [show 395 = 200 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 1 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_394_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (395 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (395 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_395 :
    recurrence4Scalar0Left.coeff 395 =
      -((((19751284147636301144132524945351575647969082696185809499574822 * 10 ^ 70 +
        8307769454350640430128543114154368588155267456392363267554230376868940) * 10 ^ 70 +
        0843438490039698962110055011187936057189227467340276891937606271877290) * 10 ^ 70 +
        7292067596583379471249155506286412960738095967262855187349329857949232) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (395 - x)) = _
  rw [show 396 = 201 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_395_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (396 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (396 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_396 :
    recurrence4Scalar0Left.coeff 396 =
      ((((8187752860633531266325260009810006771204936501048493132207148 * 10 ^ 70 +
        4679521266092559859816892952669941885649905015904949920799880651592559) * 10 ^ 70 +
        0188052622348819442154985787947642444179440420640728910208879617291780) * 10 ^ 70 +
        4186893604368915095215105960565050549061859820518611240139834113807980) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (396 - x)) = _
  rw [show 397 = 202 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 31 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_396_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (397 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (397 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_397 :
    recurrence4Scalar0Left.coeff 397 =
      -((((3198343860854018507195050294244942111456680909864733035347392 * 10 ^ 70 +
        3971116473507612052760038302989709167396716071364093891228402037769708) * 10 ^ 70 +
        5080231278438695345321248519233763118244770562818390478374925455186866) * 10 ^ 70 +
        5941854713790418228107767802538271718233589855820935101544680277952463) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (397 - x)) = _
  rw [show 398 = 203 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 30 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_397_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (398 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (398 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_398 :
    recurrence4Scalar0Left.coeff 398 =
      ((((1189211810106404413746429159853900090823788194972702694902280 * 10 ^ 70 +
        7771892780314862707248750271897430872534757493011529617988513517946670) * 10 ^ 70 +
        6925558561025502657476366840114521500931406198389135533217837938468878) * 10 ^ 70 +
        1093810014126297331941722907255638148760824613340308539243329020933224) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (398 - x)) = _
  rw [show 399 = 204 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 29 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_398_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (399 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (399 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_399 :
    recurrence4Scalar0Left.coeff 399 =
      -((((422825847040416241243548572429874139103878918307565092996057 * 10 ^ 70 +
        9218385544164640078921656758110772848200270107683510746941667143582495) * 10 ^ 70 +
        9357138395889117145621892239036400707375583448197484152037302398758210) * 10 ^ 70 +
        5039886412391883698004791072366614380486939850046539030836450372239900) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (399 - x)) = _
  rw [show 400 = 205 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 28 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_399_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (400 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (400 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_400 :
    recurrence4Scalar0Left.coeff 400 =
      ((((143900057795459888564740434704329015059234707263650851251734 * 10 ^ 70 +
        2898993384782550030509260142757754206003814151104081589081491169468310) * 10 ^ 70 +
        2982540008349724547346902623095981310998799970000675706522267822914060) * 10 ^ 70 +
        8134511900908385284513874739287140000933776650154143283939149254220993) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (400 - x)) = _
  rw [show 401 = 206 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 27 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_400_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (401 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (401 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_401 :
    recurrence4Scalar0Left.coeff 401 =
      -((((46779861763074126998602538756227875098661603652629015454294 * 10 ^ 70 +
        7924102115541735991296816377009062606925812131267061187936647108443922) * 10 ^ 70 +
        8324427508474226376286971916156287921667102969828274263580898943166032) * 10 ^ 70 +
        3611993121336068570418096634228426745038220759027150798281169053298421) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (401 - x)) = _
  rw [show 402 = 207 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 26 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_401_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (402 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (402 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_402 :
    recurrence4Scalar0Left.coeff 402 =
      ((((14446058148060816263931403912567960819297650156954730274037 * 10 ^ 70 +
        3289083732935294540149955335961623086022417713990128691809917841679816) * 10 ^ 70 +
        6638559455935674356723069450012792258186735812319839793178325437762809) * 10 ^ 70 +
        8080055770066946755600170235389606281364733366208960318212018356133741) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (402 - x)) = _
  rw [show 403 = 208 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 25 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_402_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (403 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (403 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_403 :
    recurrence4Scalar0Left.coeff 403 =
      -((((4192370481042734285386473336190088546776753262901379659527 * 10 ^ 70 +
        7324412234470827783043069608299576338027407864034548625492970091675398) * 10 ^ 70 +
        1047834813505580827130873508111119894686441988895213706611831460851995) * 10 ^ 70 +
        1261554174624262766367620982865386526752994877613158471234870522703076) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (403 - x)) = _
  rw [show 404 = 209 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 24 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_403_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (404 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (404 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_404 :
    recurrence4Scalar0Left.coeff 404 =
      ((((1119877513427549928831219895514466366005933503394013790244 * 10 ^ 70 +
        8272111274293092755159372817651248357688960940200294924412825872423216) * 10 ^ 70 +
        1043125782727214827987766170061338784591302894500654318867980399641941) * 10 ^ 70 +
        9057942367375249839179894336539819669196877074019560168376454618618866) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (404 - x)) = _
  rw [show 405 = 210 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 23 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_404_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (405 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (405 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_405 :
    recurrence4Scalar0Left.coeff 405 =
      -((((263142373992167143638194105940087640256831852241389981948 * 10 ^ 70 +
        6407270613721980303589415397244277619621299974747244300993808264942093) * 10 ^ 70 +
        9677349815581337376810360023786980589585375793497041071437751739464855) * 10 ^ 70 +
        8114799420822273004034601435741789138906849197709096904209896255475742) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (405 - x)) = _
  rw [show 406 = 211 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 22 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_405_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (406 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (406 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_406 :
    recurrence4Scalar0Left.coeff 406 =
      ((((47652931152295610769356932514310286173608767101624165845 * 10 ^ 70 +
        4766460942453117145992704518906278100959111987065778302661023573206568) * 10 ^ 70 +
        4340786330382021953091399409204645372447539394449450618863945219379572) * 10 ^ 70 +
        8969868143230336872938600900841611247038888436069218791037734371258924) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (406 - x)) = _
  rw [show 407 = 212 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 21 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_406_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (407 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (407 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_407 :
    recurrence4Scalar0Left.coeff 407 =
      -((((2400891061326046862435565594969754911843792010739161250 * 10 ^ 70 +
        4703659866397808879172297695382943424339916855238459910754834498998474) * 10 ^ 70 +
        3967541086977319712624184336140520975209723290550602523582796946188668) * 10 ^ 70 +
        0140133214980563666757146812656470201422967855284161081068111069854890) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (407 - x)) = _
  rw [show 408 = 213 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 20 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_407_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (408 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (408 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_408 :
    recurrence4Scalar0Left.coeff 408 =
      -((((3393181612745557108355429792833293028089791289789232701 * 10 ^ 70 +
        5306744947662052220177638702706353062232264496201189552631462828227346) * 10 ^ 70 +
        0494102455270981553325911880262812515077052556677359944079922484744350) * 10 ^ 70 +
        0163645227593407843993335206191528011370260428177112999245330265180348) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (408 - x)) = _
  rw [show 409 = 214 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 19 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_408_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (409 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (409 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_409 :
    recurrence4Scalar0Left.coeff 409 =
      ((((2320304179845566052915249629956914154324977677973361018 * 10 ^ 70 +
        1478833880317962934990257045951861918669485826025133111098543713738818) * 10 ^ 70 +
        5877655443659886026295911687614228049489426943779432630008830073383642) * 10 ^ 70 +
        8932284124608574328890428926394981112037696831236144179366683575674440) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (409 - x)) = _
  rw [show 410 = 215 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 18 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_409_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (410 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (410 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_410 :
    recurrence4Scalar0Left.coeff 410 =
      -((((1070179458741956119732961747393114067458612624648038776 * 10 ^ 70 +
        5225046669980917303828278796943742118517687814806613593093289850779720) * 10 ^ 70 +
        8713719461270528725180137931783807654802365834384827315418229897693842) * 10 ^ 70 +
        0234488468870183940181597072184924971149773859473226229469523809894277) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (410 - x)) = _
  rw [show 411 = 216 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 17 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_410_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (411 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (411 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_411 :
    recurrence4Scalar0Left.coeff 411 =
      ((((415364408079554801722187452178826514771286308645507813 * 10 ^ 70 +
        9711854718746183164506245187858427792650788409596137827803076907072324) * 10 ^ 70 +
        0731294915204524335439605126616800271517561019734996838680801661852346) * 10 ^ 70 +
        6756920153885351952228493028825146640043416390260150463397465098209426) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (411 - x)) = _
  rw [show 412 = 217 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 16 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_411_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (412 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (412 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_412 :
    recurrence4Scalar0Left.coeff 412 =
      -((((143424341468588634412110038653181232845810224566599556 * 10 ^ 70 +
        1163574150284997830831070919787360233322042975260121033999131055009184) * 10 ^ 70 +
        5379426125476168342614105258273245704222306412529333235726919987487826) * 10 ^ 70 +
        4897136554970051448301156984576396344502704639633467724274608827664814) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (412 - x)) = _
  rw [show 413 = 218 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 15 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_412_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (413 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (413 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_413 :
    recurrence4Scalar0Left.coeff 413 =
      ((((44635644028222665258233750307627675305022953342304654 * 10 ^ 70 +
        6131729174168181207672836995061328811862892382092251424375009832712148) * 10 ^ 70 +
        2005737352641644575164029239124668797416254066970106897027185257190804) * 10 ^ 70 +
        6444558541071649581069580076646586398850612736782363236082013133176405) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (413 - x)) = _
  rw [show 414 = 219 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 14 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_413_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (414 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (414 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_414 :
    recurrence4Scalar0Left.coeff 414 =
      -((((12346096200983800780270677365890618500858762223546823 * 10 ^ 70 +
        9727474763754635260194704552481072103839626322377958398883943994880708) * 10 ^ 70 +
        5634611251596274279944872290093871978913503585460820339453028773863965) * 10 ^ 70 +
        4776835694174413551493131613009687066672701268205184159765297759748846) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (414 - x)) = _
  rw [show 415 = 220 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 13 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_414_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (415 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (415 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_415 :
    recurrence4Scalar0Left.coeff 415 =
      ((((2857257732128003381842964707211956174896705981761852 * 10 ^ 70 +
        8470335231639797036498358495151426748870053926786801145496437270767393) * 10 ^ 70 +
        5761599499001674635850856755760381327942939830320510206095883528374435) * 10 ^ 70 +
        6159397471915541330601449751397051972389933257966531086682206488513735) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (415 - x)) = _
  rw [show 416 = 221 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 12 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_415_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (416 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (416 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_416 :
    recurrence4Scalar0Left.coeff 416 =
      -((((428210890559018278949118904090147140774155503321283 * 10 ^ 70 +
        8863870700523675813294226482543831504632575626662897139513741865112849) * 10 ^ 70 +
        8434385947025693293912787180753410584899596618044326161098388982977889) * 10 ^ 70 +
        8759344197220307169621560217478141515794602328923718956679958648855533) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (416 - x)) = _
  rw [show 417 = 222 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 11 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_416_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (417 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (417 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_417 :
    recurrence4Scalar0Left.coeff 417 =
      -((((54703378317517970253119678452185037624712872984940 * 10 ^ 70 +
        4512896082805451677450448275614470925367432823662510567874280778069335) * 10 ^ 70 +
        5289888491857268325866763461692732191578597049125237626133950140554536) * 10 ^ 70 +
        8937794223903062401498081627570564337930987290557351924076310685888792) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (417 - x)) = _
  rw [show 418 = 223 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 10 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_417_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (418 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (418 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_418 :
    recurrence4Scalar0Left.coeff 418 =
      ((((87476451023884187966489968676211491100905204107055 * 10 ^ 70 +
        7466026806530210508360492686309426976464117660429980586381610394937311) * 10 ^ 70 +
        0164747068344296077444472742728676184559074101790979302092462880968704) * 10 ^ 70 +
        9074542907395571001903769799953180445343162805530334640858088833223045) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (418 - x)) = _
  rw [show 419 = 224 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 9 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_418_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (419 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (419 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_419 :
    recurrence4Scalar0Left.coeff 419 =
      -((((52062657662228015405239096182348326819360815127981 * 10 ^ 70 +
        9492983279634877908995710095889042176979942956290109329813561839906259) * 10 ^ 70 +
        4594432140686731791220982886154868859203809629069702134465125396600017) * 10 ^ 70 +
        7681517204709755177191740346244114030340125086693237142380100933502434) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (419 - x)) = _
  rw [show 420 = 225 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 8 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_419_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (420 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (420 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_420 :
    recurrence4Scalar0Left.coeff 420 =
      ((((24526358911495304362690530631889978241691616247442 * 10 ^ 70 +
        6305407651503112716047773843857359171177610472403322085965153464784256) * 10 ^ 70 +
        2976356199522112548801597119377677800302036108831324345157659741732391) * 10 ^ 70 +
        3356608941199488654032040837619438602841172509424172683059598336080481) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (420 - x)) = _
  rw [show 421 = 226 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 7 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_420_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (421 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (421 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_421 :
    recurrence4Scalar0Left.coeff 421 =
      -((((10292867318990851416569867434280850689973158858322 * 10 ^ 70 +
        5774793727167954781238520940496830154520751704237447853680049985785487) * 10 ^ 70 +
        6921451376013253660919884550542476973255235296267357656300433475454906) * 10 ^ 70 +
        6451951951460111644681263321976771868067915881357855713564108189109076) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (421 - x)) = _
  rw [show 422 = 227 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 6 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_421_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (422 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (422 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_422 :
    recurrence4Scalar0Left.coeff 422 =
      ((((4011935456413288747446655769740680673070016957184 * 10 ^ 70 +
        8121885992392023179221724313071543451477299120993692634125768242186252) * 10 ^ 70 +
        2600413852256236437106103676191313558769315971462248028642819450297954) * 10 ^ 70 +
        1123496136423345202344145414993485222732468377536551970120167898574688) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (422 - x)) = _
  rw [show 423 = 228 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 5 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_422_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (423 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (423 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_423 :
    recurrence4Scalar0Left.coeff 423 =
      -((((1480457794171800503410755568556683265754438334006 * 10 ^ 70 +
        3503065689994638795537112559920502151289832232601856002337160421506609) * 10 ^ 70 +
        9028772305430468137180083234583938902987545484105416380099957015297991) * 10 ^ 70 +
        9316499148110250566103180646012523674737405086612076860249519028660264) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (423 - x)) = _
  rw [show 424 = 229 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 4 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_423_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (424 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (424 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_424 :
    recurrence4Scalar0Left.coeff 424 =
      ((((522316351655332224728219739981224584331705858296 * 10 ^ 70 +
        5569834583213065980955120392033372449230766296660004231858710263996578) * 10 ^ 70 +
        5739319118286512560460369198277583889080811228758329374969308947416283) * 10 ^ 70 +
        7829819513643423501105965254551207064497074449877423498626237389969398) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (424 - x)) = _
  rw [show 425 = 230 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 3 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_424_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (425 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (425 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_425 :
    recurrence4Scalar0Left.coeff 425 =
      -((((177096876696559658929637996073126362403873529010 * 10 ^ 70 +
        8359928987778996617830216369895904822816912772071731856019323860937921) * 10 ^ 70 +
        1581948883635678921313190894176477019846543348295985050025647390774841) * 10 ^ 70 +
        2223652396003228729218160699493326900113221410392675341092344201998888) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (425 - x)) = _
  rw [show 426 = 231 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 2 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_425_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (426 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (426 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_426 :
    recurrence4Scalar0Left.coeff 426 =
      ((((57848899166546141861477923266015007206208917425 * 10 ^ 70 +
        9618235820581526998120913215384892462369318091191458115985487419129571) * 10 ^ 70 +
        8570247443312934931374341476924359165207962826377561675649503565953047) * 10 ^ 70 +
        9163225331883795318234581885195151258061061815092453122697861294398993) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (426 - x)) = _
  rw [show 427 = 232 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 1 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_426_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (427 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (427 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_427 :
    recurrence4Scalar0Left.coeff 427 =
      -((((18216795910024827244366555530719094049181169480 * 10 ^ 70 +
        0042995670741800508657371673931739454426467511905841676862440620371936) * 10 ^ 70 +
        2503465664473735140134823640078759860144071766665214512957480811467124) * 10 ^ 70 +
        1044106440721332702926353334372840680068247525167032944855779167805144) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (427 - x)) = _
  rw [show 428 = 233 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_427_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (428 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (428 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_428 :
    recurrence4Scalar0Left.coeff 428 =
      ((((5526195396704808900119319684261535137738332602 * 10 ^ 70 +
        9551734164873636562284149867490893356172753427925010890035728231720156) * 10 ^ 70 +
        5511504154855260381201438921160708221452724331356524942528748676264216) * 10 ^ 70 +
        5989235918446933740926153340611937131532279827432915578924970111551619) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (428 - x)) = _
  rw [show 429 = 234 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 31 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_428_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (429 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (429 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_429 :
    recurrence4Scalar0Left.coeff 429 =
      -((((1611734269241317660391466307410290456243543739 * 10 ^ 70 +
        2732352223862945097102070521838843320579349160144727079264358555086569) * 10 ^ 70 +
        2004147633518015529462679936278828934800993609713907649556263799916732) * 10 ^ 70 +
        7287579465654637713667458329137221250978739463028077154707063206481536) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (429 - x)) = _
  rw [show 430 = 235 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 30 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_429_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (430 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (430 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_430 :
    recurrence4Scalar0Left.coeff 430 =
      ((((450406129915567948986481506198456641651549951 * 10 ^ 70 +
        4597445001402307511759260750957542576371769189116710917560068537427021) * 10 ^ 70 +
        7743035687377124120115197074002325984848705888686300638265065611257929) * 10 ^ 70 +
        1298356972741964415685956415710260479172012064353672129208872480393542) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (430 - x)) = _
  rw [show 431 = 236 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 29 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_430_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (431 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (431 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_431 :
    recurrence4Scalar0Left.coeff 431 =
      -((((119974859671746780706262372073769425481039695 * 10 ^ 70 +
        0926428044323565655698527079828226295217217459523337029590213863600634) * 10 ^ 70 +
        7425230899094063176694601602494331568244110684599385428670088252966396) * 10 ^ 70 +
        8033989888119824373984475838892084866549861520498087962540538150022910) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (431 - x)) = _
  rw [show 432 = 237 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 28 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_431_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (432 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (432 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_432 :
    recurrence4Scalar0Left.coeff 432 =
      ((((30216293284310250774799464201539950154403422 * 10 ^ 70 +
        9985518908791690565770939651124960401173070105082753718950087540152692) * 10 ^ 70 +
        0922352267848252112515602976773532042238541883537163482189476106511133) * 10 ^ 70 +
        1778108954296977996010370603987860835596428819955437290698780101798016) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (432 - x)) = _
  rw [show 433 = 238 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 27 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_432_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (433 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (433 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_433 :
    recurrence4Scalar0Left.coeff 433 =
      -((((7100825092901535680665047880809826247179366 * 10 ^ 70 +
        0036294975824808011135463328274159034321716309066284144152406333788124) * 10 ^ 70 +
        1262736574592597740384437107249364596950508607226933864570354096628060) * 10 ^ 70 +
        2936265157775507162331729970583665760850954124500276197628463358433249) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (433 - x)) = _
  rw [show 434 = 239 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 26 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (434 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (434 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_434 :
    recurrence4Scalar0Left.coeff 434 =
      ((((1519877335333583080153147442667177690540359 * 10 ^ 70 +
        6151287458153113672680514794057105429456809537551213454430106709624800) * 10 ^ 70 +
        2364505752445543034911350163938821569463051299768994145802775770421277) * 10 ^ 70 +
        8224632743233939708999082611986389623254604436897215172827949580999005) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (434 - x)) = _
  rw [show 435 = 240 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 25 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (435 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (435 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_435 :
    recurrence4Scalar0Left.coeff 435 =
      -((((281059011150625158937396554444069614466489 * 10 ^ 70 +
        3504228089690854230255508032856303690724397270089191866497990130379791) * 10 ^ 70 +
        0337359801416608717009949719980561359623352479076953588090440820572647) * 10 ^ 70 +
        4274463779490062386910628109807135918498109263929545306308566108757023) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (435 - x)) = _
  rw [show 436 = 241 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 24 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (436 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (436 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_436 :
    recurrence4Scalar0Left.coeff 436 =
      ((((38105357847376955897217268041464523080136 * 10 ^ 70 +
        5769670612061079169427969797128446416256163221324184480749642177099188) * 10 ^ 70 +
        2668802480864249251521072083861439787653179914981719102831922094837314) * 10 ^ 70 +
        7845667716409108540722272180272849432765936821215933043875530021286717) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (436 - x)) = _
  rw [show 437 = 242 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 23 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (437 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (437 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_437 :
    recurrence4Scalar0Left.coeff 437 =
      -((((265977406446595527394325643828366016927 * 10 ^ 70 +
        9234648640661787775455885277639424216679481684277751982989942422054945) * 10 ^ 70 +
        5921915449949154097440130462687463165317731136640627477886020599105752) * 10 ^ 70 +
        7660594561814384306549348286521714372236372583610743729530597881263648) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (437 - x)) = _
  rw [show 438 = 243 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 22 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (438 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (438 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_438 :
    recurrence4Scalar0Left.coeff 438 =
      -((((2336025255089592652721895630128686030428 * 10 ^ 70 +
        3140342321799845454704132842732164446414849894086850168447838756120343) * 10 ^ 70 +
        0446729440590294050327063723130120010812684121084452638709943145105051) * 10 ^ 70 +
        9488790654023998790369216039255424463200824565787311370650378290180957) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (438 - x)) = _
  rw [show 439 = 244 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 21 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (439 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (439 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_439 :
    recurrence4Scalar0Left.coeff 439 =
      ((((1145480983380559265051763677996973468154 * 10 ^ 70 +
        9063983683324787896951612595499677384549948054827038730562305987051143) * 10 ^ 70 +
        0049569834947981231231999549712415233928147992306420784197272102832310) * 10 ^ 70 +
        0907163266315988930670944893765516849692135222134622015527840506559790) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (439 - x)) = _
  rw [show 440 = 245 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 20 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (440 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (440 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_440 :
    recurrence4Scalar0Left.coeff 440 =
      -((((402581983546584226858488677325636504073 * 10 ^ 70 +
        3319244952304191224298692926356834910269829457424126965387463024640172) * 10 ^ 70 +
        5511893799902688970995882711033478447532297693152392802053253234901084) * 10 ^ 70 +
        5557251307201275973384339798120109740441117256496084226255697364618479) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (440 - x)) = _
  rw [show 441 = 246 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 19 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (441 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (441 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_441 :
    recurrence4Scalar0Left.coeff 441 =
      ((((120911453910668434270122107007771559680 * 10 ^ 70 +
        7363815954713060571407195779250851697290918679447747541045898407024398) * 10 ^ 70 +
        2947694739936692791061943769570116415010142531184888265547854227906058) * 10 ^ 70 +
        6198003997874976394392309871463644210285037400124697079029424780130723) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (441 - x)) = _
  rw [show 442 = 247 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 18 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (442 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (442 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_442 :
    recurrence4Scalar0Left.coeff 442 =
      -((((32737138221473539071806120666813541210 * 10 ^ 70 +
        7126559903731527521748123756919344483502280547004691655790202734791169) * 10 ^ 70 +
        9721360159469603332024780367268294329481609802182244013176139914496810) * 10 ^ 70 +
        2700255343567554297937756280412192176536495044423122515566237806802733) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (442 - x)) = _
  rw [show 443 = 248 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 17 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (443 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (443 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_443 :
    recurrence4Scalar0Left.coeff 443 =
      ((((8175485595351389694874733374377939603 * 10 ^ 70 +
        6655197559696977950096413437446585987904132322079170939788789367978580) * 10 ^ 70 +
        0019053916074660933867037307124657262314654180604206972001607241827748) * 10 ^ 70 +
        2362053105961387706643138144503656267426587807493078443730833248751367) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (443 - x)) = _
  rw [show 444 = 249 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 16 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (444 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (444 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_444 :
    recurrence4Scalar0Left.coeff 444 =
      -((((1904793902169644595570288735877075546 * 10 ^ 70 +
        4900869844521818768102976675333958157079071907170851793012268749948844) * 10 ^ 70 +
        3442840974520558899157099110940289973115611509240489984423283749500759) * 10 ^ 70 +
        7341840536490671441736867045098553104237578050134155732965802025208371) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (444 - x)) = _
  rw [show 445 = 250 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 15 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (445 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (445 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_445 :
    recurrence4Scalar0Left.coeff 445 =
      ((((416556063903147987151234429851172649 * 10 ^ 70 +
        1495193822699178278896311690755504785541285964666904678485621792429302) * 10 ^ 70 +
        6591868708792713732480168937044612809155298563786479655868338919782318) * 10 ^ 70 +
        9450261728712239858941647146561541736445605796660667405115836496265572) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (445 - x)) = _
  rw [show 446 = 251 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 14 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (446 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (446 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_446 :
    recurrence4Scalar0Left.coeff 446 =
      -((((85770059912940887411556499819073869 * 10 ^ 70 +
        2582084055122324817694558594140681785072767115492297685578307664865888) * 10 ^ 70 +
        6578678949320978005784464592353293092771462278220169283252526048156762) * 10 ^ 70 +
        4556056356391956423598843289311631882098371433323111986802961488317336) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (446 - x)) = _
  rw [show 447 = 252 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 13 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (447 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (447 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_447 :
    recurrence4Scalar0Left.coeff 447 =
      ((((16648025075494869171940332227516223 * 10 ^ 70 +
        6503465627493865584717034819559241705567551494240521239047488079712221) * 10 ^ 70 +
        5692046248175760124678447978140172275284025595424549512780579485056473) * 10 ^ 70 +
        3277629595673485643017977405072348784077512304225703686059421740839291) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (447 - x)) = _
  rw [show 448 = 253 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 12 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (448 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (448 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_448 :
    recurrence4Scalar0Left.coeff 448 =
      -((((3045582895736350585279278899829466 * 10 ^ 70 +
        7116344714537777919589291617354223056147996631657500694992099810590660) * 10 ^ 70 +
        8383049354355337534259590143888037898844219953057460633203014239022385) * 10 ^ 70 +
        0580558469432321565745659328868596044981152242344146094033637212984753) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (448 - x)) = _
  rw [show 449 = 254 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 11 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (449 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (449 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_449 :
    recurrence4Scalar0Left.coeff 449 =
      ((((524350332042033715240138186965935 * 10 ^ 70 +
        1507412642074593855344252230954158165314995301913471049850518009905491) * 10 ^ 70 +
        5419254321744243209865621282877842647852115848586158575541619711556797) * 10 ^ 70 +
        2972654181773116089926273920611180456026640019384253020469443855269405) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (449 - x)) = _
  rw [show 450 = 255 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 10 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (450 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (450 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_450 :
    recurrence4Scalar0Left.coeff 450 =
      -((((84716051899899078355920862856604 * 10 ^ 70 +
        3870534527823081728525278754374515998016361875754830329241854926272523) * 10 ^ 70 +
        9547775530648755420932421994425314943445719461863073737630604869613117) * 10 ^ 70 +
        7866706418656817177180222208644504326492614011112303234559356059010978) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (450 - x)) = _
  rw [show 451 = 256 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 9 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (451 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (451 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_451 :
    recurrence4Scalar0Left.coeff 451 =
      ((((12782937630894926282436665844912 * 10 ^ 70 +
        8212216651390470719983219443743717883969744920270024070428254752594350) * 10 ^ 70 +
        7853403965108302319721586626741842808517288511829381620840536116866948) * 10 ^ 70 +
        4446013241558496927774548413862502534843743042116946613684410850892754) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (451 - x)) = _
  rw [show 452 = 257 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 8 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (452 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (452 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_452 :
    recurrence4Scalar0Left.coeff 452 =
      -((((1787511679305239192396086324746 * 10 ^ 70 +
        9503169678683829773712494594583259898657963247199625989190395310895366) * 10 ^ 70 +
        2538122340295388603876859438644149871285437442271927213153554672837336) * 10 ^ 70 +
        0408729720724549033525944673855850141349273240123636630093838040311539) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (452 - x)) = _
  rw [show 453 = 258 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 7 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (453 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (453 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_453 :
    recurrence4Scalar0Left.coeff 453 =
      ((((228608306320460439445322049419 * 10 ^ 70 +
        4134030438812731821493234296189397455293943190536904921450771337049612) * 10 ^ 70 +
        9545202633484631479015740960928754406024662833257769172952259581550905) * 10 ^ 70 +
        1470454159514173903400688825487277184981078488550862341014915064473346) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (453 - x)) = _
  rw [show 454 = 259 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 6 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (454 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (454 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_454 :
    recurrence4Scalar0Left.coeff 454 =
      -((((26084906234801769128977546681 * 10 ^ 70 +
        5015248651718674686115523513786363408444539149534803597623995546133340) * 10 ^ 70 +
        1516810937627746887947024717870963916163659545857530068819548261618577) * 10 ^ 70 +
        1730689643822176479490934135153594540582418276430030230923777511723054) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (454 - x)) = _
  rw [show 455 = 260 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 5 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (455 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (455 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_455 :
    recurrence4Scalar0Left.coeff 455 =
      ((((2511485952967347485689124323 * 10 ^ 70 +
        2915475471897644145433189264435304088792642904326247278096697584303948) * 10 ^ 70 +
        3633536729196819501841719513275838265755773098592504759440542422207007) * 10 ^ 70 +
        2808149979777417776322038709600351709504271045935729581219242169151230) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (455 - x)) = _
  rw [show 456 = 261 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 4 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (456 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (456 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_456 :
    recurrence4Scalar0Left.coeff 456 =
      -((((170464934450206920348406707 * 10 ^ 70 +
        7182656182624485576701635499684613291452895358505115970691292929682322) * 10 ^ 70 +
        1615492117319290384902917074376977799374539156172769834239673623796574) * 10 ^ 70 +
        1247790402525546773194055883324481986277932124291006108827219451400119) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (456 - x)) = _
  rw [show 457 = 262 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 3 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (457 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (457 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_457 :
    recurrence4Scalar0Left.coeff 457 =
      -((((782114445600558407177154 * 10 ^ 70 +
        1216214251007969046618956654101996918283470001364406806566431540889165) * 10 ^ 70 +
        8307193660941261583598799090313255613576943327461652656499257557829999) * 10 ^ 70 +
        2608177534062421026559361893581931213245436611351471731272894221923102) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (457 - x)) = _
  rw [show 458 = 263 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 2 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (458 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (458 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_458 :
    recurrence4Scalar0Left.coeff 458 =
      ((((2970279138219661135340255 * 10 ^ 70 +
        0716965339136940373259055218330413501442906526588751652496768409464924) * 10 ^ 70 +
        2071082871361623755795426543349388733501700629447061802021116227282202) * 10 ^ 70 +
        2492011295360247198244468497645494811898789996964007491315184442385423) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (458 - x)) = _
  rw [show 459 = 264 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 1 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (459 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (459 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_459 :
    recurrence4Scalar0Left.coeff 459 =
      -((((684851764694885623899637 * 10 ^ 70 +
        1218237246183099412376541113057154161706155955474986608445344314067500) * 10 ^ 70 +
        2718268206116305502861460728698436074236249419675785515806119580092101) * 10 ^ 70 +
        9134616314954495559498103433190246995769459225598299695467546254683451) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (459 - x)) = _
  rw [show 460 = 265 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (460 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (460 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_460 :
    recurrence4Scalar0Left.coeff 460 =
      ((((112402740306963453148726 * 10 ^ 70 +
        4894037245283400001584233206881750591980950475878848638890749304517266) * 10 ^ 70 +
        1101780874390521194140937559724540387961103691856500253659096347293452) * 10 ^ 70 +
        5097427225928690900907275143521376343314590712983612804020153306434423) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (460 - x)) = _
  rw [show 461 = 266 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 31 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (461 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (461 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_461 :
    recurrence4Scalar0Left.coeff 461 =
      -((((15318203046925605826229 * 10 ^ 70 +
        2071451446323328098130464449007485237157705806238273704751197967186373) * 10 ^ 70 +
        5248040225813472109151470593265256132202099080315391307121446919346082) * 10 ^ 70 +
        8949246970781898210350254983334870804036564072979180245109247681999334) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (461 - x)) = _
  rw [show 462 = 267 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 30 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_461_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (462 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (462 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_462 :
    recurrence4Scalar0Left.coeff 462 =
      ((((1803681361867217709899 * 10 ^ 70 +
        5816059134977549744419452294228448912080198480622480030244288728302615) * 10 ^ 70 +
        1462783354890307844372386671462082091435287128663188419379685188896814) * 10 ^ 70 +
        5228922483641195506179293322684916305443648763345887906987308918687500) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (462 - x)) = _
  rw [show 463 = 268 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 29 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_462_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (463 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (463 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_463 :
    recurrence4Scalar0Left.coeff 463 =
      -((((184258016620918380677 * 10 ^ 70 +
        6604093111839596713926178924828192048819672542555190931652271063368551) * 10 ^ 70 +
        9680573690237640772648976744115479984697370542692544330420491301197934) * 10 ^ 70 +
        2701751113714751925134453470928593070352930386082859705855587724827729) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (463 - x)) = _
  rw [show 464 = 269 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 28 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_463_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (464 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (464 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_464 :
    recurrence4Scalar0Left.coeff 464 =
      ((((15979696441038758100 * 10 ^ 70 +
        6483475009637965557393470815657225119145536792369200796217758336819135) * 10 ^ 70 +
        0669096809502561287903462334367383833414360660758901241303069326615968) * 10 ^ 70 +
        1249194228780004682963678822999076437232157218783201412755710238016820) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (464 - x)) = _
  rw [show 465 = 270 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 27 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_464_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (465 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (465 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_465 :
    recurrence4Scalar0Left.coeff 465 =
      -((((1099163150635655059 * 10 ^ 70 +
        2378702912640585950743723419721687628739457910896826658062125387323268) * 10 ^ 70 +
        9249501752043327884839531011799689964533207931774674683978120931201762) * 10 ^ 70 +
        8664338522702751198486455893198158759923695035123857395914183346056632) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (465 - x)) = _
  rw [show 466 = 271 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 26 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_465_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (466 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (466 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_466 :
    recurrence4Scalar0Left.coeff 466 =
      ((((46290034165941428 * 10 ^ 70 +
        3830186665175652216482792792417612956637768137047167089300650742926033) * 10 ^ 70 +
        9670562077851233389488755315038831541405220574525449613677550000819646) * 10 ^ 70 +
        0707801801289700397396969828317967946258080634208796626460246207387891) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (466 - x)) = _
  rw [show 467 = 272 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 25 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_466_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (467 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (467 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_467 :
    recurrence4Scalar0Left.coeff 467 =
      ((((1387891292102210 * 10 ^ 70 +
        2643682394175772217257863549412774107813454761640199225797480418914996) * 10 ^ 70 +
        4635316163905031022400293964556691480115258489351578759642150986347230) * 10 ^ 70 +
        5299448681315104806516052218071823546881489854639061554797882531068135) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (467 - x)) = _
  rw [show 468 = 273 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 24 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_467_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (468 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (468 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_468 :
    recurrence4Scalar0Left.coeff 468 =
      -((((544488088855786 * 10 ^ 70 +
        6213351020176951984887244390420798339144671827656386491539008660833716) * 10 ^ 70 +
        6174862959922420926567931813657832554761243678933928557847859078725361) * 10 ^ 70 +
        1619972544858727865584102646478257317757248836579793654759726610065241) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (468 - x)) = _
  rw [show 469 = 274 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 23 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_468_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
