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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
