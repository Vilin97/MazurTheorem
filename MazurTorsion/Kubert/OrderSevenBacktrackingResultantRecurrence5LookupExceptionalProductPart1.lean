/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3Square
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptional
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: ExceptionalProduct coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence5ExceptionalProduct_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5A3Square.coeff x * exceptional5.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_217 :
    recurrence5ExceptionalProduct.coeff 217 =
      (
        -(((5070482550850203078757624800799395027124366673431084398 * 10 ^ 70 +
          5858877902872864847497375410745638099225299708758369648007854245644003) * 10 ^ 70 +
          8607354239109623600758278273469459396379415496204811880332909405738081)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 167 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5A3Square.coeff x * exceptional5.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_218 :
    recurrence5ExceptionalProduct.coeff 218 =
      (
        (((288946140221074925913783390082056952946702886536472804 * 10 ^ 70 +
          4638997073409385008221950124966986492483640276858667425328401300737121) * 10 ^ 70 +
          8308355287633308925482140896481011148464186063813258407284250365241157)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 168 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5A3Square.coeff x * exceptional5.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_219 :
    recurrence5ExceptionalProduct.coeff 219 =
      (
        -(((1559516856401783808406186144230137657870768244770491230 * 10 ^ 70 +
          2948926274812916954570201417753754442402152552704736332975481179816899) * 10 ^ 70 +
          7680543966009412916285024323748702945027163699196439380970303361384369)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 169 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5A3Square.coeff x * exceptional5.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_220 :
    recurrence5ExceptionalProduct.coeff 220 =
      (
        (((1061118122447802412630444742756542691473910135480887 * 10 ^ 70 +
          7826072951798555441755181027171662204023356075100368137614807138732123) * 10 ^ 70 +
          7340425228207280722650243811021154929728259084862971872364307572024337)) /
        (36903522622444794639665 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 170 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5A3Square.coeff x * exceptional5.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_221 :
    recurrence5ExceptionalProduct.coeff 221 =
      (
        -(((71516164987597372171854704023613009095388979897193528 * 10 ^ 70 +
          4627430340472234704123218057773727569665220023571886134874111549869061) * 10 ^ 70 +
          1346911174038669347925039254588694126585085364379535571581449415250293)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 171 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5A3Square.coeff x * exceptional5.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_222 :
    recurrence5ExceptionalProduct.coeff 222 =
      (
        (((34041848286384043762521429706262378453213306693785172 * 10 ^ 70 +
          9785983990596136321416582957886693296263542855662638088960456994576071) * 10 ^ 70 +
          7881450158943760747175128363264388882600382107440856525467726477085119)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 172 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5A3Square.coeff x * exceptional5.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_223 :
    recurrence5ExceptionalProduct.coeff 223 =
      (
        -(((31219564227976864961831366254199310846357003887391946 * 10 ^ 70 +
          5673241802178421516658400061156639407661607722330868037249474089340127) * 10 ^ 70 +
          6106357901958565689552349648109630785920901025378035638535958275235207)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 173 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5A3Square.coeff x * exceptional5.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_224 :
    recurrence5ExceptionalProduct.coeff 224 =
      (
        -(((11872846567389193413470497031519867128243835055286554 * 10 ^ 70 +
          6919147666462503657688530328023650431612266644835666275137908391296640) * 10 ^ 70 +
          0798673164738884944454157513082499745481303623286154007875705710173717)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 174 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5A3Square.coeff x * exceptional5.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_225 :
    recurrence5ExceptionalProduct.coeff 225 =
      (
        (((6157685242010434365628491730243632301298246415445269 * 10 ^ 70 +
          3451310266288562892339843868468404100695028336829783685201969584760785) * 10 ^ 70 +
          8311663440871132358532572215369851221420168627390577390201586084112878)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 175 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5A3Square.coeff x * exceptional5.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_226 :
    recurrence5ExceptionalProduct.coeff 226 =
      (
        -(((1209861510958004671729556997259003514982764991860935 * 10 ^ 70 +
          8133334224523343868276514176284778434488021212196465600263991153867356) * 10 ^ 70 +
          8817606629076077146761806650287141870943874923441669630680448919985936)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 176 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence5A3Square.coeff x * exceptional5.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_227 :
    recurrence5ExceptionalProduct.coeff 227 =
      (
        (((9616808805340933970126087043298627335244162847631832 * 10 ^ 70 +
          6254859993345707663407106735341956854986845694981038933154176150840821) * 10 ^ 70 +
          6292026699940389650587206278211638042182967530301582460777518710547361)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 177 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence5A3Square.coeff x * exceptional5.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_228 :
    recurrence5ExceptionalProduct.coeff 228 =
      (
        -(((3420771113053639637790289276517521711030591344378825 * 10 ^ 70 +
          7839993708115489144389044512896684141174007004193432664566241800644452) * 10 ^ 70 +
          1156838249971625253441814005134668090344555251307120057933755120873908)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 178 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence5A3Square.coeff x * exceptional5.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_229 :
    recurrence5ExceptionalProduct.coeff 229 =
      (
        (((2260152896061157399703049277372064059593330288716395 * 10 ^ 70 +
          6570137826954742679323601984425689070828776806377581651741847202534283) * 10 ^ 70 +
          6346041289306391795710037541684917129519317798176684848116195157022321)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 179 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence5A3Square.coeff x * exceptional5.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_230 :
    recurrence5ExceptionalProduct.coeff 230 =
      (
        -(((225736921729731441998231991095975373139839858189377 * 10 ^ 70 +
          3343699235997929635298262226392363039038912780745612386532765440915634) * 10 ^ 70 +
          4211557315627901200389381013012621726457552961628396575565138534013545)) /
        (1092344269624365921334084 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 180 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence5A3Square.coeff x * exceptional5.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_231 :
    recurrence5ExceptionalProduct.coeff 231 =
      (
        (((18146582467884456048353412200525823356689585103335 * 10 ^ 70 +
          2888121975198876264967999864986031194466304787671201598824087388485251) * 10 ^ 70 +
          6950385659116482529457847048270821039604404564449707518499381744705277)) /
        (147614090489779178558660 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 181 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence5A3Square.coeff x * exceptional5.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_232 :
    recurrence5ExceptionalProduct.coeff 232 =
      (
        -(((382171355022271373833211197042595326594271197862386 * 10 ^ 70 +
          7882333896203668333044827665040502047351242921797370991338974511475882) * 10 ^ 70 +
          6951408239832536861212517906615307072991412000832859487853516357140957)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 182 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence5A3Square.coeff x * exceptional5.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_233 :
    recurrence5ExceptionalProduct.coeff 233 =
      (
        (((260417267355248839517936601641377575194663733929112 * 10 ^ 70 +
          6211626681524470531257082789794367560209995472042903887506069409404902) * 10 ^ 70 +
          7398403726901102145027227738466523109587447384736328669451253169731939)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 183 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence5A3Square.coeff x * exceptional5.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_234 :
    recurrence5ExceptionalProduct.coeff 234 =
      (
        -(((271406562600918517635085534154738553383601079766841 * 10 ^ 70 +
          7122006202770119533910551102058962644067774575243813647268326483349358) * 10 ^ 70 +
          4353902174575727339951076634800977801578805018657461430052097239360051)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 184 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence5A3Square.coeff x * exceptional5.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_235 :
    recurrence5ExceptionalProduct.coeff 235 =
      (
        (((67237834512160507410019014093707965404411483999835 * 10 ^ 70 +
          0773790645447431328526944681916904163405783201237509942728684010072473) * 10 ^ 70 +
          2884240299691673962693483123378220299762812360874216173239104524960401)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 185 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence5A3Square.coeff x * exceptional5.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_236 :
    recurrence5ExceptionalProduct.coeff 236 =
      (
        -(((62670653259752800453199223162653886023486526404455 * 10 ^ 70 +
          1775129100262826448401536487710406805055078910683123840615432966696890) * 10 ^ 70 +
          3021831509520958775908271339745427582509024237772201466611807880763239)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 186 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence5A3Square.coeff x * exceptional5.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_237 :
    recurrence5ExceptionalProduct.coeff 237 =
      (
        (((13438315060508488608279301390524427718846115926528 * 10 ^ 70 +
          6766498062697574224264565640315551223228040894385418787734364865854257) * 10 ^ 70 +
          6283013813836036364966356564323731392018027121231343279921293332607762)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 187 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence5A3Square.coeff x * exceptional5.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_238 :
    recurrence5ExceptionalProduct.coeff 238 =
      (
        -(((20171738999129629789301699712832224255262985289059 * 10 ^ 70 +
          2171992953928730295996547079582311266178170997418417307463263893004249) * 10 ^ 70 +
          8410229637261611869221372093115194911924053073290552710220336739727299)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 188 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence5A3Square.coeff x * exceptional5.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_239 :
    recurrence5ExceptionalProduct.coeff 239 =
      (
        (((1129769227090160106100488426354442413089971739550 * 10 ^ 70 +
          6906956482887005102704500546040606625177606203163176648594424552261926) * 10 ^ 70 +
          9990452425232001292155302168950250539161039944215221073374775458356919)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 189 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence5A3Square.coeff x * exceptional5.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_240 :
    recurrence5ExceptionalProduct.coeff 240 =
      (
        -(((122152219531884218427113440220902802242390249059 * 10 ^ 70 +
          7449332549416272631287998316883651207942245832021004698087404863818720) * 10 ^ 70 +
          0735802733304460727194765772759743566987856097293222465894509692496849)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 190 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence5A3Square.coeff x * exceptional5.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_241 :
    recurrence5ExceptionalProduct.coeff 241 =
      (
        -(((370904966307534017587460108639459106086401245916 * 10 ^ 70 +
          8403616590041230864164232868809451362785569452885824158394300858641271) * 10 ^ 70 +
          7383908865689453899514877263534274241238409719395191481401469659925846)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 191 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence5A3Square.coeff x * exceptional5.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_242 :
    recurrence5ExceptionalProduct.coeff 242 =
      (
        (((15784082812049157810777464245359080510602259348 * 10 ^ 70 +
          2286151442298619731119205583324520488622521043075338184535400665297786) * 10 ^ 70 +
          4572602195774066960467242771036040002090300085042141119326998259238979)) /
        (273086067406091480333521 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 192 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence5A3Square.coeff x * exceptional5.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_243 :
    recurrence5ExceptionalProduct.coeff 243 =
      (
        -(((122015221468542672921180328702166432479260408712 * 10 ^ 70 +
          9850742315873242057282395396014234920013461415352489244329616519370543) * 10 ^ 70 +
          4697166702067502333389898503183399054321039223371446939763692715757151)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 193 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence5A3Square.coeff x * exceptional5.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_244 :
    recurrence5ExceptionalProduct.coeff 244 =
      (
        (((5548496032035726759335203390340142661739782148 * 10 ^ 70 +
          3271141086842481731630062681853782238795212115388799619890763849877503) * 10 ^ 70 +
          3969209827613241776684453713712559713009077795464302354464527190389239)) /
        (184517613112223973198325 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 194 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence5A3Square.coeff x * exceptional5.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_245 :
    recurrence5ExceptionalProduct.coeff 245 =
      (
        -(((127125497143243129407538924425440360718545909359 * 10 ^ 70 +
          7284877449811338283152334258922587408104364598894567979267028569565178) * 10 ^ 70 +
          6151641250204998347996322349862251111839610821509466243532303142497021)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 195 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence5A3Square.coeff x * exceptional5.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_246 :
    recurrence5ExceptionalProduct.coeff 246 =
      (
        (((74203125618687313903259117262728547938857609842 * 10 ^ 70 +
          6358934865307055621807433518324937912152588868663021331962536573928498) * 10 ^ 70 +
          4099839704290210865307772677347135189751342405164030292817022907132667)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 196 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence5A3Square.coeff x * exceptional5.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_247 :
    recurrence5ExceptionalProduct.coeff 247 =
      (
        -(((82686797307359042204723069303186694425426607502 * 10 ^ 70 +
          5327214978265806138905103376657245045325169076155265988265153912229048) * 10 ^ 70 +
          9895310045642778023768361616746165583760687317254457672151851997375607)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 197 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence5A3Square.coeff x * exceptional5.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_248 :
    recurrence5ExceptionalProduct.coeff 248 =
      (
        (((88585692379919792742907096109898708932906179077 * 10 ^ 70 +
          5645099785518199390541628389692728072835030342159082966874237808060853) * 10 ^ 70 +
          2754103233917176718821291689122377802718040086762551602649928040309361)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 198 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence5A3Square.coeff x * exceptional5.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_249 :
    recurrence5ExceptionalProduct.coeff 249 =
      (
        -(((1238324342516331305356794521060059031034480149 * 10 ^ 70 +
          4628662168613444311386649314750479009759117304220364646773065648125793) * 10 ^ 70 +
          7966683968414895404085968538801698752804161623603446958228013792593903)) /
        (738070452448895892793300 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 199 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence5A3Square.coeff x * exceptional5.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_250 :
    recurrence5ExceptionalProduct.coeff 250 =
      (
        (((22939939938366466088059176593426439720420922153 * 10 ^ 70 +
          3440116717252511477026977236486759652653493305568839600861297607646226) * 10 ^ 70 +
          7767458404008077287797538797786194812149128550712661471048252581274053)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 200 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence5A3Square.coeff x * exceptional5.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_251 :
    recurrence5ExceptionalProduct.coeff 251 =
      (
        -(((1113385237852696679339597935472502150288223392 * 10 ^ 70 +
          1525017169565626267655935659239549822713904855062757654047506822539600) * 10 ^ 70 +
          9169706039579979550760373569825217091028178304820338283548963357877493)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 201 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence5A3Square.coeff x * exceptional5.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_252 :
    recurrence5ExceptionalProduct.coeff 252 =
      (
        (((5241481104901005885139991478215545639776850401 * 10 ^ 70 +
          6314797272855634812340508647428665860229403394277261775673728400363212) * 10 ^ 70 +
          6866793710349891111000266523701940854005872949758958595859313619837891)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 202 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence5A3Square.coeff x * exceptional5.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_253 :
    recurrence5ExceptionalProduct.coeff 253 =
      (
        -(((2393298990011923877869085227606642614516930252 * 10 ^ 70 +
          7214451142179188684550530218728104346949207770366909637667890725568428) * 10 ^ 70 +
          3999080081048880086185082965354586222590356637847737616982258894260963)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 203 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence5A3Square.coeff x * exceptional5.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_254 :
    recurrence5ExceptionalProduct.coeff 254 =
      (
        (((21185536398430754564553637156121286664315086 * 10 ^ 70 +
          0394777261858938948761455370259762680778608945313944298091102612154364) * 10 ^ 70 +
          9399607009753644846493888351567309090646012033611245461321796136902611)) /
        (546172134812182960667042 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 204 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence5A3Square.coeff x * exceptional5.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_255 :
    recurrence5ExceptionalProduct.coeff 255 =
      (
        -(((90785794088554341845199320272999388843294511 * 10 ^ 70 +
          4702170730576612936893005097336649259097524448575612401950138060443751) * 10 ^ 70 +
          3573233544156950576577118147435090670662503676404585971021641810231739)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 205 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence5A3Square.coeff x * exceptional5.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_256 :
    recurrence5ExceptionalProduct.coeff 256 =
      (
        (((188002813533716024357331800438560400199256279 * 10 ^ 70 +
          3688697403374588054999505196859235144117336319273719944800937641857792) * 10 ^ 70 +
          7000462163146438801965175491478863906891343587182382506812220608442081)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 206 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence5A3Square.coeff x * exceptional5.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_257 :
    recurrence5ExceptionalProduct.coeff 257 =
      (
        -(((37532945857685448257140745965872449868773253 * 10 ^ 70 +
          7478834001300284572535432565255152706076025976818969808304608334265196) * 10 ^ 70 +
          2368860222121756099682831290588245623041147225234427704492006880190029)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 207 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence5A3Square.coeff x * exceptional5.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_258 :
    recurrence5ExceptionalProduct.coeff 258 =
      (
        (((7198038623395290171273740478178289363570472 * 10 ^ 70 +
          5033877273424564093303100998882632025720670205482127524189348718285761) * 10 ^ 70 +
          5658430063075917950314014965359695761937325674428567638811190665721509)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 208 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence5A3Square.coeff x * exceptional5.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_259 :
    recurrence5ExceptionalProduct.coeff 259 =
      (
        -(((5277098359900864882986637346962308606269849 * 10 ^ 70 +
          2107433341525904257105614030087988163342768820528635314061834998108668) * 10 ^ 70 +
          5595669522968630980327599284644435524299037169326157080202661803951231)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 209 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence5A3Square.coeff x * exceptional5.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_260 :
    recurrence5ExceptionalProduct.coeff 260 =
      (
        (((3668802775283294796859799126676963782591877 * 10 ^ 70 +
          8243931959622275345636016343971354819115749075940857156672239473137964) * 10 ^ 70 +
          7134420100652461746604140331709275065278186704947851830104717093770337)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 210 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence5A3Square.coeff x * exceptional5.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_261 :
    recurrence5ExceptionalProduct.coeff 261 =
      (
        -(((47771003560827778788010359273446315361529 * 10 ^ 70 +
          9887202467657363985745388929182211741029366771787613584398915370271593) * 10 ^ 70 +
          0269068612588620093150926705196515001447508217767266529521823046760619)) /
        (1092344269624365921334084 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 211 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence5A3Square.coeff x * exceptional5.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_262 :
    recurrence5ExceptionalProduct.coeff 262 =
      (
        (((71172230022126832427772026064154956793329 * 10 ^ 70 +
          1775276863978026368159209242445998442172238373456966496173243131689884) * 10 ^ 70 +
          5283686791269777588325765638209559761744328968869466411812743728281137)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 212 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence5A3Square.coeff x * exceptional5.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_263 :
    recurrence5ExceptionalProduct.coeff 263 =
      (
        -(((46213248278164795593794943656760186589901 * 10 ^ 70 +
          6795681222731433857482662075583349912090437897835881512262926359563263) * 10 ^ 70 +
          4591922884656141960149156810538543820903876272200900396626935889941933)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 213 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence5A3Square.coeff x * exceptional5.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_264 :
    recurrence5ExceptionalProduct.coeff 264 =
      (
        (((18086098509168081270391247136095382142137 * 10 ^ 70 +
          6952850923372036427028532513256508932964911426520375463424503716789438) * 10 ^ 70 +
          3974647745452948077351823321415130038461932929865982910063646397384171)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 214 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence5A3Square.coeff x * exceptional5.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_265 :
    recurrence5ExceptionalProduct.coeff 265 =
      (
        -(((662151873334928204218505743302450667289 * 10 ^ 70 +
          4350056613390840590792876892049193461330426493467462838490126444710161) * 10 ^ 70 +
          4344632008229462294972160927391263325736695444947601367294452047801177)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 215 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence5A3Square.coeff x * exceptional5.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_266 :
    recurrence5ExceptionalProduct.coeff 266 =
      (
        -(((452180290170649140751834065314061524476 * 10 ^ 70 +
          6316665703376772629999522498236339989694003576002122102258374419097201) * 10 ^ 70 +
          2407210537512407748010253867325143592180776504860620871277103827685866)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 216 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence5A3Square.coeff x * exceptional5.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_267 :
    recurrence5ExceptionalProduct.coeff 267 =
      (
        (((51817429165007476920562097431181835685 * 10 ^ 70 +
          1419522120866546121320132958275408060135865190827644081831695643883187) * 10 ^ 70 +
          1362757680951315345326820137029000987928148626721170217708914807560859)) /
        (1092344269624365921334084 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 217 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence5A3Square.coeff x * exceptional5.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_268 :
    recurrence5ExceptionalProduct.coeff 268 =
      (
        -(((64251494341114576977193957068561208781 * 10 ^ 70 +
          7859662345398970920879948273282989374889281660742427880193641105268291) * 10 ^ 70 +
          6489619879623210521570074743133402091514079833180679921557524377046589)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 218 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence5A3Square.coeff x * exceptional5.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_269 :
    recurrence5ExceptionalProduct.coeff 269 =
      (
        (((53791493244814027827341190689982668358 * 10 ^ 70 +
          2282017236362406893896850545650936169019261427334630003822210061841385) * 10 ^ 70 +
          8825682362121041285668920719113964519540986276205223101925092854123921)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 219 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_269_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence5A3Square.coeff x * exceptional5.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_270 :
    recurrence5ExceptionalProduct.coeff 270 =
      (
        -(((25049939246660146611646472040446321711 * 10 ^ 70 +
          5542199883777864612492472412595826516138060353090438999767310115623342) * 10 ^ 70 +
          2265595918672501795937970262285782959405315987989931103519296379912941)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 220 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_270_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence5A3Square.coeff x * exceptional5.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_271 :
    recurrence5ExceptionalProduct.coeff 271 =
      (
        (((6746449254898487958593294248886472029 * 10 ^ 70 +
          2152108310847189919731082600128739765768534620835779983860651141341190) * 10 ^ 70 +
          7243203510298848499373033081820301055011898718838949470607838446632459)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 221 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_271_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence5A3Square.coeff x * exceptional5.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_272 :
    recurrence5ExceptionalProduct.coeff 272 =
      (
        -(((10198577550024844195414498758133936567 * 10 ^ 70 +
          3753912112428824174887227223601300708422581945468681559299484318655961) * 10 ^ 70 +
          2942685793887354053846394679703319349657568271395470163771989378547361)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 222 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_272_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence5A3Square.coeff x * exceptional5.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_273 :
    recurrence5ExceptionalProduct.coeff 273 =
      (
        (((1336160455518235172191898046751426211 * 10 ^ 70 +
          9460029285058986035673743046938165923106370648915066448261016719734264) * 10 ^ 70 +
          2837116497244339445796861869990840542954856324644171657292714882003673)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 223 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_273_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence5A3Square.coeff x * exceptional5.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_274 :
    recurrence5ExceptionalProduct.coeff 274 =
      (
        -(((53549545709424675430783372455443704 * 10 ^ 70 +
          9943369745747236497622765247634036928285400069055234764207321174006137) * 10 ^ 70 +
          0753439219652115535681695281480244570496121543893304151216760306907211)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 224 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_274_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence5A3Square.coeff x * exceptional5.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_275 :
    recurrence5ExceptionalProduct.coeff 275 =
      (
        (((7365965149627348009536135170668136 * 10 ^ 70 +
          0625221356384526517477349394776596594957983378338994807886664929851324) * 10 ^ 70 +
          4014643397599310456400763999983365795816641326930123881757137736220441)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 225 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_275_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence5A3Square.coeff x * exceptional5.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_276 :
    recurrence5ExceptionalProduct.coeff 276 =
      (
        (((23650950092311123428160720674142411 * 10 ^ 70 +
          5712588631839022360512350669190114023387721201422590048172787848989630) * 10 ^ 70 +
          1420257326370630309296153408120396038047712896585895855732876517443239)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 226 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_276_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence5A3Square.coeff x * exceptional5.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_277 :
    recurrence5ExceptionalProduct.coeff 277 =
      (
        -(((9086256218645684495676428632520038 * 10 ^ 70 +
          9325889136052073163193305584810151153474083644276214296994699954774107) * 10 ^ 70 +
          4486885844078207848118506673436635262767070674024058549073780197283288)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 227 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_277_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence5A3Square.coeff x * exceptional5.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_278 :
    recurrence5ExceptionalProduct.coeff 278 =
      (
        (((19178698019680666916501457917015124 * 10 ^ 70 +
          7747403198069473511838033077579046463723243291553440937771389024781277) * 10 ^ 70 +
          7862747197964261956002100288313671005973622769129921579289416579064921)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 228 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_278_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence5A3Square.coeff x * exceptional5.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_279 :
    recurrence5ExceptionalProduct.coeff 279 =
      (
        -(((8712631429588842232264876464981003 * 10 ^ 70 +
          7840424823663992554001590634144212545725418618073469807935751609475671) * 10 ^ 70 +
          3292878930291808715366632077741511154184110242947867791502420405771377)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 229 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_279_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence5A3Square.coeff x * exceptional5.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_280 :
    recurrence5ExceptionalProduct.coeff 280 =
      (
        (((1814374107448176716498709458086105 * 10 ^ 70 +
          9960620766700991786808420526980487246864089055033392960559450936866679) * 10 ^ 70 +
          3839424521971607025712391691638561264635649496001125785095743522428009)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 230 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_280_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence5A3Square.coeff x * exceptional5.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_281 :
    recurrence5ExceptionalProduct.coeff 281 =
      (
        -(((1420727049519216506028244040319447 * 10 ^ 70 +
          1974169690166088159063092193634482146187878907952921580077347320996800) * 10 ^ 70 +
          7401369678524299551818250689993511972344863166362265896284589665796241)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 231 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_281_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence5A3Square.coeff x * exceptional5.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_282 :
    recurrence5ExceptionalProduct.coeff 282 =
      (
        (((264238080587017793136657087926545 * 10 ^ 70 +
          8527214389739402814685406297168853214607984009346689042216536160866310) * 10 ^ 70 +
          8080565332879350099601987423680461753707130621360427623542033150699627)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 232 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_282_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence5A3Square.coeff x * exceptional5.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_283 :
    recurrence5ExceptionalProduct.coeff 283 =
      (
        -(((187396781865430380915036522784752 * 10 ^ 70 +
          8694269796099279325715715753967922762501861927872512207270047718798524) * 10 ^ 70 +
          3055395469776053757922376975159380192084689025497550708258972850612253)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 233 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_283_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence5A3Square.coeff x * exceptional5.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_284 :
    recurrence5ExceptionalProduct.coeff 284 =
      (
        (((1265174300958424566070567050849 * 10 ^ 70 +
          3934568202650445164248273032780708168468656271109340612557080149544956) * 10 ^ 70 +
          7840745631294707782289932386895440720333737052250611671735501209222397)) /
        (546172134812182960667042 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 234 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_284_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence5A3Square.coeff x * exceptional5.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_285 :
    recurrence5ExceptionalProduct.coeff 285 =
      (
        -(((4042356987409087768854795575335 * 10 ^ 70 +
          8829914648900274394471406707398620496608450757881618551659485660742663) * 10 ^ 70 +
          8099954383026484255109987042199367639769917260013077172074616083095091)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 235 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_285_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence5A3Square.coeff x * exceptional5.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_286 :
    recurrence5ExceptionalProduct.coeff 286 =
      (
        (((3020669092269737440060858968588 * 10 ^ 70 +
          9196242713728886203247487436784238971508873732555863625120840177944349) * 10 ^ 70 +
          7108299925538439259393724683935417288702008433246625247701640148064227)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 236 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_286_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence5A3Square.coeff x * exceptional5.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_287 :
    recurrence5ExceptionalProduct.coeff 287 =
      (
        -(((1650826091063126339054393037483 * 10 ^ 70 +
          5846647937656200452374890307773721675398498745261808165511345997403197) * 10 ^ 70 +
          7543735383088425478584261509081672494619665594155422833014348679624459)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 237 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_287_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence5A3Square.coeff x * exceptional5.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_288 :
    recurrence5ExceptionalProduct.coeff 288 =
      (
        (((78315637929371536817357043353 * 10 ^ 70 +
          6161508640748375154241689872710324319176894259723837705830671618948649) * 10 ^ 70 +
          9938201047795743578052576558066529761928256661805756746258855887086911)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 238 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_288_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence5A3Square.coeff x * exceptional5.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_289 :
    recurrence5ExceptionalProduct.coeff 289 =
      (
        -(((34304378938891013641204909487 * 10 ^ 70 +
          8634990047301255464405285429000274032761096977874670038841418216210957) * 10 ^ 70 +
          8097898965773632473181029179371214777606250884409842380174074458787149)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 239 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_289_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence5A3Square.coeff x * exceptional5.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_290 :
    recurrence5ExceptionalProduct.coeff 290 =
      (
        (((860097655113501502225049860 * 10 ^ 70 +
          8879060412845480792978497682943252969985431217406191766168813761355539) * 10 ^ 70 +
          6779676383770133171113806647170573452280315175933914973848763868875737)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 240 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence5A3Square.coeff x * exceptional5.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_291 :
    recurrence5ExceptionalProduct.coeff 291 =
      (
        (((6862457961221508615095476794 * 10 ^ 70 +
          6744159004449565026942120998362339398260327305933265866520568006265333) * 10 ^ 70 +
          3733755281217926648621027866712357486933150282412578318277650672222971)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 241 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_291_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence5A3Square.coeff x * exceptional5.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_292 :
    recurrence5ExceptionalProduct.coeff 292 =
      (
        -(((877243826617315927645349419 * 10 ^ 70 +
          5655170225686522989063553622296556304239328175054896806043629787705045) * 10 ^ 70 +
          6228039774260006384081534878449799543685944995224123605197790755468439)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 242 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_292_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence5A3Square.coeff x * exceptional5.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_293 :
    recurrence5ExceptionalProduct.coeff 293 =
      (
        (((500248092002436396642160473 * 10 ^ 70 +
          0923842778306722185686396129100227787893382567115116188378594523439592) * 10 ^ 70 +
          5615464243379037545385792051159785390101520914088634631503863037966859)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 243 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_293_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence5A3Square.coeff x * exceptional5.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_294 :
    recurrence5ExceptionalProduct.coeff 294 =
      (
        -(((194309578656437639849101305 * 10 ^ 70 +
          4151635088179089762383237128242489823276664199302712317838758497058499) * 10 ^ 70 +
          5579235242693514301567459328379005754130763148929483288409281186102514)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 244 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_294_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence5A3Square.coeff x * exceptional5.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_295 :
    recurrence5ExceptionalProduct.coeff 295 =
      (
        (((67567150342974434198237442 * 10 ^ 70 +
          7444968438114098982416654593344272780316354905673290124224320113905655) * 10 ^ 70 +
          4654791939176852220721763028984405354768153295580435817779891407103898)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 245 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_295_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence5A3Square.coeff x * exceptional5.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_296 :
    recurrence5ExceptionalProduct.coeff 296 =
      (
        -(((85520340417176762432473463 * 10 ^ 70 +
          3793921755888411759519954212112331773265745519448371745674224719848311) * 10 ^ 70 +
          1034170187088475825520590880830046657698767115319308070156902578338777)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 246 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_296_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence5A3Square.coeff x * exceptional5.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_297 :
    recurrence5ExceptionalProduct.coeff 297 =
      (
        (((24582985857964516022130688 * 10 ^ 70 +
          9267260311969221364339233276887761655876351104216462003647171002076692) * 10 ^ 70 +
          7794845237542412143416011139815200888079925237415032628267673546713737)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 247 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_297_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence5A3Square.coeff x * exceptional5.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_298 :
    recurrence5ExceptionalProduct.coeff 298 =
      (
        -(((6268826435721986445105603 * 10 ^ 70 +
          3882512650734910334821565612647094441052595736848278291599012141987012) * 10 ^ 70 +
          8538399597001446793992657225218487384625974913281245472778098127281913)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 248 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_298_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence5A3Square.coeff x * exceptional5.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_299 :
    recurrence5ExceptionalProduct.coeff 299 =
      (
        (((130879437229144502688510 * 10 ^ 70 +
          3969339262862557865715401193253152726247702610392363019281480106078533) * 10 ^ 70 +
          6254868369054076137842252051475071658466384119734285238238644662642087)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 249 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_299_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence5A3Square.coeff x * exceptional5.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_300 :
    recurrence5ExceptionalProduct.coeff 300 =
      (
        -(((37538639748316194002031 * 10 ^ 70 +
          0851497435700809152353525737618350536741843695920235898581062267309384) * 10 ^ 70 +
          5931140155349001591693143026128873261661105862746882779687835321530587)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 250 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_300_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence5A3Square.coeff x * exceptional5.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_301 :
    recurrence5ExceptionalProduct.coeff 301 =
      (
        -(((12074773673350830485749 * 10 ^ 70 +
          5245374531139319073396175150849948924150641984461114341513891228185815) * 10 ^ 70 +
          3727927264208316830902219303162928019803841682009161153424495327086382)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 251 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_301_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence5A3Square.coeff x * exceptional5.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_302 :
    recurrence5ExceptionalProduct.coeff 302 =
      (
        (((9674738941314203980097 * 10 ^ 70 +
          9736564936828822093664784921637671867010602749484778607121436716078804) * 10 ^ 70 +
          5490659161592186026397117460993767128357137964657616137848066648959773)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 252 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_302_prefix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence5A3Square.coeff x * exceptional5.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (343 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_343 :
    recurrence5ExceptionalProduct.coeff 343 =
      (
        ((7582197290111909381421328635098845963352371611160117738703541828 * 10 ^ 70 +
          6907906357427714071197671715511613701509049365022500756935774269678917)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 293 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence5A3Square.coeff x * exceptional5.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (344 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_344 :
    recurrence5ExceptionalProduct.coeff 344 =
      (
        -((204205471249649880589362071227466510801474048124190862534765133 * 10 ^ 70 +
          1214445241703841171216559952246328720592412323141466655899031588967741)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 294 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence5A3Square.coeff x * exceptional5.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (345 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_345 :
    recurrence5ExceptionalProduct.coeff 345 =
      (
        ((263986427114562881725370650821534679870772001494187681528089 * 10 ^ 70 +
          0643371081266209383411487476831421382534295175200062730509433214088807)) /
        (184517613112223973198325 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 295 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence5A3Square.coeff x * exceptional5.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (346 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_346 :
    recurrence5ExceptionalProduct.coeff 346 =
      (
        -((328299462392443913875649644621377250626084740072553840119038 * 10 ^ 70 +
          4381716177737281577040414181880120007604519034103140050505273018630717)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 296 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence5A3Square.coeff x * exceptional5.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (347 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_347 :
    recurrence5ExceptionalProduct.coeff 347 =
      (
        ((59758307906542643461522475534133869497259335204930321055493 * 10 ^ 70 +
          1612783805163677549924174115823711471540863791155652701738383583303907)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 297 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence5A3Square.coeff x * exceptional5.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (348 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_348 :
    recurrence5ExceptionalProduct.coeff 348 =
      (
        -((1852041798144544892675068888538525203065723081664136968679 * 10 ^ 70 +
          0787265236530834336405142003247072133060771134392645439794312508701617)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 298 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence5A3Square.coeff x * exceptional5.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (349 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_349 :
    recurrence5ExceptionalProduct.coeff 349 =
      (
        ((4770453453130049493920931285106307513318115038479649467 * 10 ^ 70 +
          4342773381594348765284520222616660769644955163230977844538107244951551)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 299 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence5A3Square.coeff x * exceptional5.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (350 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_350 :
    recurrence5ExceptionalProduct.coeff 350 =
      (
        -((246449568717182431709627267134405216370557522334994649 * 10 ^ 70 +
          0956193205692904025940368159732633808240646682160582315189048009985096)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 300 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence5A3Square.coeff x * exceptional5.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (351 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_351 :
    recurrence5ExceptionalProduct.coeff 351 =
      (
        ((154076707605336035765544053340397841535334260159000 * 10 ^ 70 +
          3451854878848101881027282249442928607919081960790974929590662607490185)) /
        (273086067406091480333521 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 301 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence5A3Square.coeff x * exceptional5.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (352 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_352 :
    recurrence5ExceptionalProduct.coeff 352 =
      (
        -((160640596721525440088820926188065499964091469356298 * 10 ^ 70 +
          2813270221386080972976792583163528749725152269763427077516870092506643)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 302 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence5A3Square.coeff x * exceptional5.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (353 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_353 :
    recurrence5ExceptionalProduct.coeff 353 =
      (
        ((672541224962670143011351225785205791314141198606 * 10 ^ 70 +
          9952148279553709844753590276071902122097753089927235095860400957690873)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 303 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence5A3Square.coeff x * exceptional5.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (354 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_354 :
    recurrence5ExceptionalProduct.coeff 354 =
      (
        ((1958292914456142551211501868297012317931495480 * 10 ^ 70 +
          0853267306125519930803125713636748346425396765604159790681038369402706)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 304 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence5A3Square.coeff x * exceptional5.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (355 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_355 :
    recurrence5ExceptionalProduct.coeff 355 =
      (
        -((128757643071223541211091554584829113598702958 * 10 ^ 70 +
          5614637967822324082033224814087347936190008497707704306954267332611911)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 305 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence5A3Square.coeff x * exceptional5.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (356 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_356 :
    recurrence5ExceptionalProduct.coeff 356 =
      (
        ((384045207830181277296159096709757468287017 * 10 ^ 70 +
          6417605444654982014987874756594626657064742313225915330628233757657247)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 306 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence5A3Square.coeff x * exceptional5.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (357 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_357 :
    recurrence5ExceptionalProduct.coeff 357 =
      (
        ((2236030982006977252179387511306034942023 * 10 ^ 70 +
          6838214960620279235281797548633451027283051827392119307765313145421483)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 307 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence5A3Square.coeff x * exceptional5.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (358 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_358 :
    recurrence5ExceptionalProduct.coeff 358 =
      (
        -((29541263647844232707574902367062086816 * 10 ^ 70 +
          5546038946731655814531092634002474420411242670628710015211981704470403)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 308 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence5A3Square.coeff x * exceptional5.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (359 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_359 :
    recurrence5ExceptionalProduct.coeff 359 =
      (
        -((43925810107717830038716976337951609 * 10 ^ 70 +
          6899822804117434950661463361981616001761662693565664107124684615193633)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 309 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence5A3Square.coeff x * exceptional5.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (360 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_360 :
    recurrence5ExceptionalProduct.coeff 360 =
      (
        ((331587602193031627477641773192578 * 10 ^ 70 +
          1051119937696162650083424619671654194920172115416116312094921167529157)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 310 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence5A3Square.coeff x * exceptional5.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (361 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_361 :
    recurrence5ExceptionalProduct.coeff 361 =
      (
        -((542832619886123277997316862386 * 10 ^ 70 +
          3486315025451789991769706136700413102855827703392408673113167444258621)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 311 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence5A3Square.coeff x * exceptional5.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (362 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_362 :
    recurrence5ExceptionalProduct.coeff 362 =
      (
        -((1466851697128710092172271778 * 10 ^ 70 +
          5223520641403365346343268337730178674438261623388757573924235461825013)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 312 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence5A3Square.coeff x * exceptional5.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (363 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_363 :
    recurrence5ExceptionalProduct.coeff 363 =
      (
        ((13681334102978870378166860 * 10 ^ 70 +
          6454660127463254878534387438790119304499451105132869966714655722118229)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 313 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence5A3Square.coeff x * exceptional5.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (364 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_364 :
    recurrence5ExceptionalProduct.coeff 364 =
      (
        ((860284965020279453707 * 10 ^ 70 +
          2915074759728688126659646062692188420556522486308922748966871048618931)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 314 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence5A3Square.coeff x * exceptional5.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (365 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_365 :
    recurrence5ExceptionalProduct.coeff 365 =
      (
        -((13589867853889713505 * 10 ^ 70 +
          2227573640694823246104737658977084746086565172515998047286661021450007)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 315 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence5A3Square.coeff x * exceptional5.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (366 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_366 :
    recurrence5ExceptionalProduct.coeff 366 =
      (
        ((101231014933921148 * 10 ^ 70 +
          8763047239082891627559475266675388284788393817917374950301013834721501)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 316 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 13 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence5A3Square.coeff x * exceptional5.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (367 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_367 :
    recurrence5ExceptionalProduct.coeff 367 =
      (
        -((17788973154982 * 10 ^ 70 +
          4257989170013289402629550167417187320934475852853250051161883520662753)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 317 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence5A3Square.coeff x * exceptional5.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (368 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_368 :
    recurrence5ExceptionalProduct.coeff 368 =
      (
        ((13017865323 * 10 ^ 70 +
          1681734961776809568008417042199244613127943107965238348350197896180287)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 318 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence5A3Square.coeff x * exceptional5.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (369 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_369 :
    recurrence5ExceptionalProduct.coeff 369 =
      (
        -((2465235 * 10 ^ 70 +
          5323208847078780429496406443222801428345773441090479151627933895638107)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 319 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 10 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence5A3Square.coeff x * exceptional5.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (370 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_370 :
    recurrence5ExceptionalProduct.coeff 370 =
      (
        ((118 * 10 ^ 70 +
          0700282994780651352612433478058520405535331938697583239871074270908174)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 320 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence5A3Square.coeff x * exceptional5.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (371 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_371 :
    recurrence5ExceptionalProduct.coeff 371 =
      (
        (-21504891122472802553208266381028656288787472711548297392529514222757) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 321 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 8 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence5A3Square.coeff x * exceptional5.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (372 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_372 :
    recurrence5ExceptionalProduct.coeff 372 =
      (
        (224013240194473025830142321787928855379984989101925825663648982) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 322 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence5A3Square.coeff x * exceptional5.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (373 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_373 :
    recurrence5ExceptionalProduct.coeff 373 =
      (
        (-377985129306735110447359789354935170640294104296055234979) /
        (273086067406091480333521 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 323 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence5A3Square.coeff x * exceptional5.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (374 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_374 :
    recurrence5ExceptionalProduct.coeff 374 =
      (
        (126172775470916960259126666597957781024616544005586033) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 324 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence5A3Square.coeff x * exceptional5.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (375 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_375 :
    recurrence5ExceptionalProduct.coeff 375 =
      (
        (-126517018144915947155277336042476635597329697857) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 325 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence5A3Square.coeff x * exceptional5.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (376 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_376 :
    recurrence5ExceptionalProduct.coeff 376 =
      (
        (41618300119571719020429822932379579198849) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 326 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence5A3Square.coeff x * exceptional5.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (377 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_377 :
    recurrence5ExceptionalProduct.coeff 377 =
      (
        (-195586437252026034978) /
        (2612881873555 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 327 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence5A3Square.coeff x * exceptional5.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5ExceptionalProduct_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5A3Square.coeff (329 + x) *
        exceptional5.coeff (378 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3Square_coeff_high (329 + x) (by omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_378 :
    recurrence5ExceptionalProduct.coeff 378 =
      (1 : ℚ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 328 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5ExceptionalProduct_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
