/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3Square
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptional
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProductPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: ExceptionalProduct coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5A3Square_coeff_0
  recurrence5A3Square_coeff_1
  recurrence5A3Square_coeff_2
  recurrence5A3Square_coeff_3
  recurrence5A3Square_coeff_4
  recurrence5A3Square_coeff_5
  recurrence5A3Square_coeff_6
  recurrence5A3Square_coeff_7
  recurrence5A3Square_coeff_8
  recurrence5A3Square_coeff_9
  recurrence5A3Square_coeff_10
  recurrence5A3Square_coeff_11
  recurrence5A3Square_coeff_12
  recurrence5A3Square_coeff_13
  recurrence5A3Square_coeff_14
  recurrence5A3Square_coeff_15
  recurrence5A3Square_coeff_16
  recurrence5A3Square_coeff_17
  recurrence5A3Square_coeff_18
  recurrence5A3Square_coeff_19
  recurrence5A3Square_coeff_20
  recurrence5A3Square_coeff_21
  recurrence5A3Square_coeff_22
  recurrence5A3Square_coeff_23
  recurrence5A3Square_coeff_24
  recurrence5A3Square_coeff_25
  recurrence5A3Square_coeff_26
  recurrence5A3Square_coeff_27
  recurrence5A3Square_coeff_28
  recurrence5A3Square_coeff_29
  recurrence5A3Square_coeff_30
  recurrence5A3Square_coeff_31
  recurrence5A3Square_coeff_32
  recurrence5A3Square_coeff_33
  recurrence5A3Square_coeff_34
  recurrence5A3Square_coeff_35
  recurrence5A3Square_coeff_36
  recurrence5A3Square_coeff_37
  recurrence5A3Square_coeff_38
  recurrence5A3Square_coeff_39
  recurrence5A3Square_coeff_40
  recurrence5A3Square_coeff_41
  recurrence5A3Square_coeff_42
  recurrence5A3Square_coeff_43
  recurrence5A3Square_coeff_44
  recurrence5A3Square_coeff_45
  recurrence5A3Square_coeff_46
  recurrence5A3Square_coeff_47
  recurrence5A3Square_coeff_48
  recurrence5A3Square_coeff_49
  recurrence5A3Square_coeff_50
  recurrence5A3Square_coeff_51
  recurrence5A3Square_coeff_52
  recurrence5A3Square_coeff_53
  recurrence5A3Square_coeff_54
  recurrence5A3Square_coeff_55
  recurrence5A3Square_coeff_56
  recurrence5A3Square_coeff_57
  recurrence5A3Square_coeff_58
  recurrence5A3Square_coeff_59
  recurrence5A3Square_coeff_60
  recurrence5A3Square_coeff_61
  recurrence5A3Square_coeff_62
  recurrence5A3Square_coeff_63

attribute [local simp]
  recurrence5A3Square_coeff_64
  recurrence5A3Square_coeff_65
  recurrence5A3Square_coeff_66
  recurrence5A3Square_coeff_67
  recurrence5A3Square_coeff_68
  recurrence5A3Square_coeff_69
  recurrence5A3Square_coeff_70
  recurrence5A3Square_coeff_71
  recurrence5A3Square_coeff_72
  recurrence5A3Square_coeff_73
  recurrence5A3Square_coeff_74
  recurrence5A3Square_coeff_75
  recurrence5A3Square_coeff_76
  recurrence5A3Square_coeff_77
  recurrence5A3Square_coeff_78
  recurrence5A3Square_coeff_79
  recurrence5A3Square_coeff_80
  recurrence5A3Square_coeff_81
  recurrence5A3Square_coeff_82
  recurrence5A3Square_coeff_83
  recurrence5A3Square_coeff_84
  recurrence5A3Square_coeff_85
  recurrence5A3Square_coeff_86
  recurrence5A3Square_coeff_87
  recurrence5A3Square_coeff_88
  recurrence5A3Square_coeff_89
  recurrence5A3Square_coeff_90
  recurrence5A3Square_coeff_91
  recurrence5A3Square_coeff_92
  recurrence5A3Square_coeff_93
  recurrence5A3Square_coeff_94
  recurrence5A3Square_coeff_95
  recurrence5A3Square_coeff_96
  recurrence5A3Square_coeff_97
  recurrence5A3Square_coeff_98
  recurrence5A3Square_coeff_99
  recurrence5A3Square_coeff_100
  recurrence5A3Square_coeff_101
  recurrence5A3Square_coeff_102
  recurrence5A3Square_coeff_103
  recurrence5A3Square_coeff_104
  recurrence5A3Square_coeff_105
  recurrence5A3Square_coeff_106
  recurrence5A3Square_coeff_107
  recurrence5A3Square_coeff_108
  recurrence5A3Square_coeff_109
  recurrence5A3Square_coeff_110
  recurrence5A3Square_coeff_111
  recurrence5A3Square_coeff_112
  recurrence5A3Square_coeff_113
  recurrence5A3Square_coeff_114
  recurrence5A3Square_coeff_115
  recurrence5A3Square_coeff_116
  recurrence5A3Square_coeff_117
  recurrence5A3Square_coeff_118
  recurrence5A3Square_coeff_119
  recurrence5A3Square_coeff_120
  recurrence5A3Square_coeff_121
  recurrence5A3Square_coeff_122
  recurrence5A3Square_coeff_123
  recurrence5A3Square_coeff_124
  recurrence5A3Square_coeff_125
  recurrence5A3Square_coeff_126
  recurrence5A3Square_coeff_127

attribute [local simp]
  recurrence5A3Square_coeff_128
  recurrence5A3Square_coeff_129
  recurrence5A3Square_coeff_130
  recurrence5A3Square_coeff_131
  recurrence5A3Square_coeff_132
  recurrence5A3Square_coeff_133
  recurrence5A3Square_coeff_134
  recurrence5A3Square_coeff_135
  recurrence5A3Square_coeff_136
  recurrence5A3Square_coeff_137
  recurrence5A3Square_coeff_138
  recurrence5A3Square_coeff_139
  recurrence5A3Square_coeff_140
  recurrence5A3Square_coeff_141
  recurrence5A3Square_coeff_142
  recurrence5A3Square_coeff_143
  recurrence5A3Square_coeff_144
  recurrence5A3Square_coeff_145
  recurrence5A3Square_coeff_146
  recurrence5A3Square_coeff_147
  recurrence5A3Square_coeff_148
  recurrence5A3Square_coeff_149
  recurrence5A3Square_coeff_150
  recurrence5A3Square_coeff_151
  recurrence5A3Square_coeff_152
  recurrence5A3Square_coeff_153
  recurrence5A3Square_coeff_154
  recurrence5A3Square_coeff_155
  recurrence5A3Square_coeff_156
  recurrence5A3Square_coeff_157
  recurrence5A3Square_coeff_158
  recurrence5A3Square_coeff_159
  recurrence5A3Square_coeff_160
  recurrence5A3Square_coeff_161
  recurrence5A3Square_coeff_162
  recurrence5A3Square_coeff_163
  recurrence5A3Square_coeff_164
  recurrence5A3Square_coeff_165
  recurrence5A3Square_coeff_166
  recurrence5A3Square_coeff_167
  recurrence5A3Square_coeff_168
  recurrence5A3Square_coeff_169
  recurrence5A3Square_coeff_170
  recurrence5A3Square_coeff_171
  recurrence5A3Square_coeff_172
  recurrence5A3Square_coeff_173
  recurrence5A3Square_coeff_174
  recurrence5A3Square_coeff_175
  recurrence5A3Square_coeff_176
  recurrence5A3Square_coeff_177
  recurrence5A3Square_coeff_178
  recurrence5A3Square_coeff_179
  recurrence5A3Square_coeff_180
  recurrence5A3Square_coeff_181
  recurrence5A3Square_coeff_182
  recurrence5A3Square_coeff_183
  recurrence5A3Square_coeff_184
  recurrence5A3Square_coeff_185
  recurrence5A3Square_coeff_186
  recurrence5A3Square_coeff_187
  recurrence5A3Square_coeff_188
  recurrence5A3Square_coeff_189
  recurrence5A3Square_coeff_190
  recurrence5A3Square_coeff_191

attribute [local simp]
  recurrence5A3Square_coeff_192
  recurrence5A3Square_coeff_193
  recurrence5A3Square_coeff_194
  recurrence5A3Square_coeff_195
  recurrence5A3Square_coeff_196
  recurrence5A3Square_coeff_197
  recurrence5A3Square_coeff_198
  recurrence5A3Square_coeff_199
  recurrence5A3Square_coeff_200
  recurrence5A3Square_coeff_201
  recurrence5A3Square_coeff_202
  recurrence5A3Square_coeff_203
  recurrence5A3Square_coeff_204
  recurrence5A3Square_coeff_205
  recurrence5A3Square_coeff_206
  recurrence5A3Square_coeff_207
  recurrence5A3Square_coeff_208
  recurrence5A3Square_coeff_209
  recurrence5A3Square_coeff_210
  recurrence5A3Square_coeff_211
  recurrence5A3Square_coeff_212
  recurrence5A3Square_coeff_213
  recurrence5A3Square_coeff_214
  recurrence5A3Square_coeff_215
  recurrence5A3Square_coeff_216
  recurrence5A3Square_coeff_217
  recurrence5A3Square_coeff_218
  recurrence5A3Square_coeff_219
  recurrence5A3Square_coeff_220
  recurrence5A3Square_coeff_221
  recurrence5A3Square_coeff_222
  recurrence5A3Square_coeff_223
  recurrence5A3Square_coeff_224
  recurrence5A3Square_coeff_225
  recurrence5A3Square_coeff_226
  recurrence5A3Square_coeff_227
  recurrence5A3Square_coeff_228
  recurrence5A3Square_coeff_229
  recurrence5A3Square_coeff_230
  recurrence5A3Square_coeff_231
  recurrence5A3Square_coeff_232
  recurrence5A3Square_coeff_233
  recurrence5A3Square_coeff_234
  recurrence5A3Square_coeff_235
  recurrence5A3Square_coeff_236
  recurrence5A3Square_coeff_237
  recurrence5A3Square_coeff_238
  recurrence5A3Square_coeff_239
  recurrence5A3Square_coeff_240
  recurrence5A3Square_coeff_241
  recurrence5A3Square_coeff_242
  recurrence5A3Square_coeff_243
  recurrence5A3Square_coeff_244
  recurrence5A3Square_coeff_245
  recurrence5A3Square_coeff_246
  recurrence5A3Square_coeff_247
  recurrence5A3Square_coeff_248
  recurrence5A3Square_coeff_249
  recurrence5A3Square_coeff_250
  recurrence5A3Square_coeff_251
  recurrence5A3Square_coeff_252
  recurrence5A3Square_coeff_253
  recurrence5A3Square_coeff_254
  recurrence5A3Square_coeff_255

attribute [local simp]
  recurrence5A3Square_coeff_256
  recurrence5A3Square_coeff_257
  recurrence5A3Square_coeff_258
  recurrence5A3Square_coeff_259
  recurrence5A3Square_coeff_260
  recurrence5A3Square_coeff_261
  recurrence5A3Square_coeff_262
  recurrence5A3Square_coeff_263
  recurrence5A3Square_coeff_264
  recurrence5A3Square_coeff_265
  recurrence5A3Square_coeff_266
  recurrence5A3Square_coeff_267
  recurrence5A3Square_coeff_268
  recurrence5A3Square_coeff_269
  recurrence5A3Square_coeff_270
  recurrence5A3Square_coeff_271
  recurrence5A3Square_coeff_272
  recurrence5A3Square_coeff_273
  recurrence5A3Square_coeff_274
  recurrence5A3Square_coeff_275
  recurrence5A3Square_coeff_276
  recurrence5A3Square_coeff_277
  recurrence5A3Square_coeff_278
  recurrence5A3Square_coeff_279
  recurrence5A3Square_coeff_280
  recurrence5A3Square_coeff_281
  recurrence5A3Square_coeff_282
  recurrence5A3Square_coeff_283
  recurrence5A3Square_coeff_284
  recurrence5A3Square_coeff_285
  recurrence5A3Square_coeff_286
  recurrence5A3Square_coeff_287
  recurrence5A3Square_coeff_288
  recurrence5A3Square_coeff_289
  recurrence5A3Square_coeff_290
  recurrence5A3Square_coeff_291
  recurrence5A3Square_coeff_292
  recurrence5A3Square_coeff_293
  recurrence5A3Square_coeff_294
  recurrence5A3Square_coeff_295
  recurrence5A3Square_coeff_296
  recurrence5A3Square_coeff_297
  recurrence5A3Square_coeff_298
  recurrence5A3Square_coeff_299
  recurrence5A3Square_coeff_300
  recurrence5A3Square_coeff_301
  recurrence5A3Square_coeff_302
  recurrence5A3Square_coeff_303
  recurrence5A3Square_coeff_304
  recurrence5A3Square_coeff_305
  recurrence5A3Square_coeff_306
  recurrence5A3Square_coeff_307
  recurrence5A3Square_coeff_308
  recurrence5A3Square_coeff_309
  recurrence5A3Square_coeff_310
  recurrence5A3Square_coeff_311
  recurrence5A3Square_coeff_312
  recurrence5A3Square_coeff_313
  recurrence5A3Square_coeff_314
  recurrence5A3Square_coeff_315
  recurrence5A3Square_coeff_316
  recurrence5A3Square_coeff_317
  recurrence5A3Square_coeff_318
  recurrence5A3Square_coeff_319

attribute [local simp]
  recurrence5A3Square_coeff_320
  recurrence5A3Square_coeff_321
  recurrence5A3Square_coeff_322
  recurrence5A3Square_coeff_323
  recurrence5A3Square_coeff_324
  recurrence5A3Square_coeff_325
  recurrence5A3Square_coeff_326
  recurrence5A3Square_coeff_327
  recurrence5A3Square_coeff_328
  recurrence5Exceptional_coeff_0
  recurrence5Exceptional_coeff_1
  recurrence5Exceptional_coeff_2
  recurrence5Exceptional_coeff_3
  recurrence5Exceptional_coeff_4
  recurrence5Exceptional_coeff_5
  recurrence5Exceptional_coeff_6
  recurrence5Exceptional_coeff_7
  recurrence5Exceptional_coeff_8
  recurrence5Exceptional_coeff_9
  recurrence5Exceptional_coeff_10
  recurrence5Exceptional_coeff_11
  recurrence5Exceptional_coeff_12
  recurrence5Exceptional_coeff_13
  recurrence5Exceptional_coeff_14
  recurrence5Exceptional_coeff_15
  recurrence5Exceptional_coeff_16
  recurrence5Exceptional_coeff_17
  recurrence5Exceptional_coeff_18
  recurrence5Exceptional_coeff_19
  recurrence5Exceptional_coeff_20
  recurrence5Exceptional_coeff_21
  recurrence5Exceptional_coeff_22
  recurrence5Exceptional_coeff_23
  recurrence5Exceptional_coeff_24
  recurrence5Exceptional_coeff_25
  recurrence5Exceptional_coeff_26
  recurrence5Exceptional_coeff_27
  recurrence5Exceptional_coeff_28
  recurrence5Exceptional_coeff_29
  recurrence5Exceptional_coeff_30
  recurrence5Exceptional_coeff_31
  recurrence5Exceptional_coeff_32
  recurrence5Exceptional_coeff_33
  recurrence5Exceptional_coeff_34
  recurrence5Exceptional_coeff_35
  recurrence5Exceptional_coeff_36
  recurrence5Exceptional_coeff_37
  recurrence5Exceptional_coeff_38
  recurrence5Exceptional_coeff_39
  recurrence5Exceptional_coeff_40
  recurrence5Exceptional_coeff_41
  recurrence5Exceptional_coeff_42
  recurrence5Exceptional_coeff_43
  recurrence5Exceptional_coeff_44
  recurrence5Exceptional_coeff_45
  recurrence5Exceptional_coeff_46
  recurrence5Exceptional_coeff_47
  recurrence5Exceptional_coeff_48
  recurrence5Exceptional_coeff_49
  recurrence5Exceptional_coeff_50

private theorem recurrence5ExceptionalProduct_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence5A3Square.coeff x * exceptional5.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_303 :
    recurrence5ExceptionalProduct.coeff 303 =
      (
        -(((5257408570997693248642 * 10 ^ 70 +
          3304046149068527800338679752384839235911315418818159804942781035159980) * 10 ^ 70 +
          0887383746302513159068865991057158335227511912614620037068380046532527)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 253 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_303_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence5A3Square.coeff x * exceptional5.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_304 :
    recurrence5ExceptionalProduct.coeff 304 =
      (
        (((2954635679898342737077 * 10 ^ 70 +
          9544101415468578099251465648145546173118469420978438866217370969007812) * 10 ^ 70 +
          5528956958285243948684385807178839701095751783196917269120199241479634)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 254 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_304_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence5A3Square.coeff x * exceptional5.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_305 :
    recurrence5ExceptionalProduct.coeff 305 =
      (
        -(((4804503319645411774064 * 10 ^ 70 +
          6591581507479850495461343678237887888911237079362630727107033483654295) * 10 ^ 70 +
          1090151768382308616635358528716666930532702786312139615304117886773581)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 255 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_305_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence5A3Square.coeff x * exceptional5.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_306 :
    recurrence5ExceptionalProduct.coeff 306 =
      (
        (((364993752578561961003 * 10 ^ 70 +
          4644164772933589921629014989638344970127601238034329346504041005304320) * 10 ^ 70 +
          7147303926008614857548395752336036216759342799252917014615721571755849)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 256 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_306_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence5A3Square.coeff x * exceptional5.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_307 :
    recurrence5ExceptionalProduct.coeff 307 =
      (
        -(((328659275303495616250 * 10 ^ 70 +
          4080926795717506114871625740735823711467036364977872420655962536924441) * 10 ^ 70 +
          7307833624099420334863821330380937097850638505757536131637243225483649)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 257 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_307_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence5A3Square.coeff x * exceptional5.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_308 :
    recurrence5ExceptionalProduct.coeff 308 =
      (
        (((226011574397341964558 * 10 ^ 70 +
          7793702313104187622705269354466489946990339216385852965790648801523253) * 10 ^ 70 +
          8083562426388653520803101464461596842136119285662733102350980460796659)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 258 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_308_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence5A3Square.coeff x * exceptional5.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_309 :
    recurrence5ExceptionalProduct.coeff 309 =
      (
        -(((74349967250895229638 * 10 ^ 70 +
          0976041806495301126965727399779188830627454003154466914976743235422384) * 10 ^ 70 +
          0620763283769522892186063974119151415371501860240201217897037852843033)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 259 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_309_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence5A3Square.coeff x * exceptional5.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_310 :
    recurrence5ExceptionalProduct.coeff 310 =
      (
        (((631794915626572828 * 10 ^ 70 +
          2768286544526970733301639932193362937544176407725378337769046417587266) * 10 ^ 70 +
          6336551471025899359911796097303474189764977478028246777071045836039257)) /
        (738070452448895892793300 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 260 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_310_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence5A3Square.coeff x * exceptional5.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_311 :
    recurrence5ExceptionalProduct.coeff 311 =
      (
        -(((1749191706348660415 * 10 ^ 70 +
          1679486692941522120874010544836962900611380268462661517201049804629829) * 10 ^ 70 +
          9108793702501175164906511602988673590727961992808171461028052132945804)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 261 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_311_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence5A3Square.coeff x * exceptional5.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_312 :
    recurrence5ExceptionalProduct.coeff 312 =
      (
        (((494768647796408364 * 10 ^ 70 +
          7575141492140896055776758984496231482426910302491288495643160487904134) * 10 ^ 70 +
          6931573371816149684883168553930535425057594328578411451632264547622342)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 262 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_312_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence5A3Square.coeff x * exceptional5.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_313 :
    recurrence5ExceptionalProduct.coeff 313 =
      (
        -(((130653250530948076 * 10 ^ 70 +
          8508032720488684203308624061516796803135570009681924654386525230501529) * 10 ^ 70 +
          1374073016087800399815859052596538466771172503526987534486200352683594)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 263 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_313_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence5A3Square.coeff x * exceptional5.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_314 :
    recurrence5ExceptionalProduct.coeff 314 =
      (
        (((31531727444336553 * 10 ^ 70 +
          2741546109196923830963005217487703729287368470029635282915341618173188) * 10 ^ 70 +
          0440070165630005466111665223592133502134610294734968302983460421117682)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 264 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_314_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence5A3Square.coeff x * exceptional5.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_315 :
    recurrence5ExceptionalProduct.coeff 315 =
      (
        -(((6660617468659714 * 10 ^ 70 +
          1674129016015389657069123518831155515187148394707758864629908143665416) * 10 ^ 70 +
          7177557707886537605182087975256009665350534399634474020277287671577702)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 265 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_315_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence5A3Square.coeff x * exceptional5.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_316 :
    recurrence5ExceptionalProduct.coeff 316 =
      (
        (((175108478219092 * 10 ^ 70 +
          7229175915709439957699350013591418597365598436382642206948243442967485) * 10 ^ 70 +
          8943674968127466122867257531560274476632540607943487110648910230473145)) /
        (1092344269624365921334084 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 266 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_316_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence5A3Square.coeff x * exceptional5.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_317 :
    recurrence5ExceptionalProduct.coeff 317 =
      (
        -(((53753338210177 * 10 ^ 70 +
          7265452323785428943543747876419261646422558957220981957698802321742076) * 10 ^ 70 +
          5194682918496131528411950376786810963454055524538461740390179688387293)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 267 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_317_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence5A3Square.coeff x * exceptional5.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_318 :
    recurrence5ExceptionalProduct.coeff 318 =
      (
        -(((188154583636307 * 10 ^ 70 +
          8673895239522118677456772605229843419954586609629453875023827398459836) * 10 ^ 70 +
          6830865406375427678243915681774970251304017079473310205748111900350631)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 268 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_318_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence5A3Square.coeff x * exceptional5.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_319 :
    recurrence5ExceptionalProduct.coeff 319 =
      (
        (((11654296128916 * 10 ^ 70 +
          4396197118000385667968836079396077298344515060823126314502421222682100) * 10 ^ 70 +
          1380113585214643750996981274912531171117286609503650299131098068977621)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 269 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_319_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence5A3Square.coeff x * exceptional5.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_320 :
    recurrence5ExceptionalProduct.coeff 320 =
      (
        -(((2291305765841 * 10 ^ 70 +
          6312078641031560056844543023550364726402892701442733337368965160597275) * 10 ^ 70 +
          7968011146420324457402154516646423433629938273266728714717526283762088)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 270 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_320_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence5A3Square.coeff x * exceptional5.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_321 :
    recurrence5ExceptionalProduct.coeff 321 =
      (
        (((3729936773944 * 10 ^ 70 +
          1618633979318017127480707499564604431552195728438585161719149619498676) * 10 ^ 70 +
          4271120378807977044934404054799288133658590775352035078364747895998926)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 271 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_321_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence5A3Square.coeff x * exceptional5.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_322 :
    recurrence5ExceptionalProduct.coeff 322 =
      (
        -(((1077398324935 * 10 ^ 70 +
          3850410433928891514684349536534363472755950766209549931321088836133498) * 10 ^ 70 +
          1264470381422740792867329669648207484981449506091937199973797032536501)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 272 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_322_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence5A3Square.coeff x * exceptional5.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_323 :
    recurrence5ExceptionalProduct.coeff 323 =
      (
        (((15348835039 * 10 ^ 70 +
          1484796243962643740909077902562920094627766972337627960875015129590082) * 10 ^ 70 +
          2051724235777012484783378484229329595333627542648070358211110212121977)) /
        (369035226224447946396650 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 273 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_323_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence5A3Square.coeff x * exceptional5.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_324 :
    recurrence5ExceptionalProduct.coeff 324 =
      (
        -(((27692933472 * 10 ^ 70 +
          8627052358524317989213838104171709808397551540328027236206383902030184) * 10 ^ 70 +
          0241467354251586419162792136593478242088473621826854774544045892274519)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 274 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_324_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence5A3Square.coeff x * exceptional5.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_325 :
    recurrence5ExceptionalProduct.coeff 325 =
      (
        (((6293361698 * 10 ^ 70 +
          0506222827660106821761214268383474413513100781465909809238846702507217) * 10 ^ 70 +
          1063846855571604378652845403586928541296408060119321960423045477950539)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 275 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_325_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence5A3Square.coeff x * exceptional5.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_326 :
    recurrence5ExceptionalProduct.coeff 326 =
      (
        -(((13387330199 * 10 ^ 70 +
          7787747295817114876193999043723120980942775435062910043200524229210795) * 10 ^ 70 +
          7515356730361063332607933432849778427091883394629279495224100779551849)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 276 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_326_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence5A3Square.coeff x * exceptional5.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_327 :
    recurrence5ExceptionalProduct.coeff 327 =
      (
        (((2671945959 * 10 ^ 70 +
          0335201865442054399896438703094515720428162461092016205783863896004186) * 10 ^ 70 +
          4883751070899260951166736031122166844920095471695963633688276073114981)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 277 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_327_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence5A3Square.coeff x * exceptional5.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_328 :
    recurrence5ExceptionalProduct.coeff 328 =
      (
        -(((500942234 * 10 ^ 70 +
          1255938524709231200633898269745170040804314707036852205875640060591369) * 10 ^ 70 +
          4930764615699866441850328674524989223193118268371706495830195525541131)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 278 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_328_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence5A3Square.coeff x * exceptional5.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_329 :
    recurrence5ExceptionalProduct.coeff 329 =
      (
        (((4412561 * 10 ^ 70 +
          8674447825545753125220476730068076982784288834897091068180177940318102) * 10 ^ 70 +
          0669752269527297283855602398531998773861693660370901294673159386739058)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 279 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence5A3Square.coeff x * exceptional5.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (330 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_330 :
    recurrence5ExceptionalProduct.coeff 330 =
      (
        -(((3651339 * 10 ^ 70 +
          1985357504264585688961311895267521272279533737035480806262884152954072) * 10 ^ 70 +
          8416137060997951529145050454714908297726496621633329370442643191727064)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 280 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 17 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence5A3Square.coeff x * exceptional5.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (331 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_331 :
    recurrence5ExceptionalProduct.coeff 331 =
      (
        (((1134519 * 10 ^ 70 +
          9163524440089742360335811239676157672532051734265412953779843082611655) * 10 ^ 70 +
          6988796213827392380805662634894730069555280687288047317209397124729661)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 281 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 16 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence5A3Square.coeff x * exceptional5.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (332 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_332 :
    recurrence5ExceptionalProduct.coeff 332 =
      (
        -(((165268 * 10 ^ 70 +
          8469039586204211916220005269819785298495846714265858662823793273570291) * 10 ^ 70 +
          0057008320348188843928473370496361093537933874350787159776993800780629)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 282 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 15 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence5A3Square.coeff x * exceptional5.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (333 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_333 :
    recurrence5ExceptionalProduct.coeff 333 =
      (
        (((22541 * 10 ^ 70 +
          3156211430317061031903266345211144013408946147995980092935344044504499) * 10 ^ 70 +
          9715709564463980407519347446171418343738463695193094918466417650552851)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 283 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 14 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence5A3Square.coeff x * exceptional5.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (334 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_334 :
    recurrence5ExceptionalProduct.coeff 334 =
      (
        -(((5746 * 10 ^ 70 +
          8193550616919213793411578933262014063252245229536832748307582307968553) * 10 ^ 70 +
          6077257939856200130704262220850901161507103391182082781799731058887389)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 284 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 13 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence5A3Square.coeff x * exceptional5.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (335 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_335 :
    recurrence5ExceptionalProduct.coeff 335 =
      (
        (((683 * 10 ^ 70 +
          2175595152030797750079402004280977188323284739865169823942942434260748) * 10 ^ 70 +
          2561095458221093590010198108912775059207251694824810602451576331895191)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 285 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 12 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence5A3Square.coeff x * exceptional5.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (336 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_336 :
    recurrence5ExceptionalProduct.coeff 336 =
      (
        -(((18 * 10 ^ 70 +
          8923194520463007587830928701936532449569588721333314831594070444777785) * 10 ^ 70 +
          9984372844401080425444502723845896947450371522091654326181717819548276)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 286 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 11 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence5A3Square.coeff x * exceptional5.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (337 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_337 :
    recurrence5ExceptionalProduct.coeff 337 =
      (
        (((1 * 10 ^ 70 +
          5509804684660227281341545078923948584016875304641119394000913205958034) * 10 ^ 70 +
          0994463841327757556930868286537919833828519820634417123594006569147557)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 287 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 10 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence5A3Square.coeff x * exceptional5.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (338 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_338 :
    recurrence5ExceptionalProduct.coeff 338 =
      (
        -((7359946853665670940795698378012010811120283416099447515591289398728702 * 10 ^ 70 +
          2488520607107108998831273262269052708038335548567312553799734065862517)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 288 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence5A3Square.coeff x * exceptional5.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (339 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_339 :
    recurrence5ExceptionalProduct.coeff 339 =
      (
        ((160920958499834557701133595538379729599563872265142293799821596117960 * 10 ^ 70 +
          3719587632684497289430547976725405165140789771299976969282131814225722)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 289 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 8 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence5A3Square.coeff x * exceptional5.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (340 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_340 :
    recurrence5ExceptionalProduct.coeff 340 =
      (
        -((12915810721850819730268630845187683005434695463361429459873462487262 * 10 ^ 70 +
          5628469095960103356339670880649450678094918319141832398874997231070418)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 290 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 7 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence5A3Square.coeff x * exceptional5.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (341 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_341 :
    recurrence5ExceptionalProduct.coeff 341 =
      (
        ((946873617974393075011933025481417935680181584922803763426325445316 * 10 ^ 70 +
          7095829880998342345306959588716066613365196248936035618459358145390519)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 291 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 6 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5ExceptionalProduct_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence5A3Square.coeff x * exceptional5.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (342 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_342 :
    recurrence5ExceptionalProduct.coeff 342 =
      (
        -((12612119366028136319782234689941108496809757823495398558843663141 * 10 ^ 70 +
          3140236560673929004944073455503301410784019919229762118770958528839039)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 292 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
