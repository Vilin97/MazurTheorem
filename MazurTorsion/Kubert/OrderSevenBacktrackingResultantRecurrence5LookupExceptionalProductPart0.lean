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

theorem recurrence5ExceptionalProduct_coeff_0 :
    recurrence5ExceptionalProduct.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_1 :
    recurrence5ExceptionalProduct.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_2 :
    recurrence5ExceptionalProduct.coeff 2 =
      (
        (68008294656) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_3 :
    recurrence5ExceptionalProduct.coeff 3 =
      (
        (-319773505615488) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_4 :
    recurrence5ExceptionalProduct.coeff 4 =
      (
        (666861526892758896) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_5 :
    recurrence5ExceptionalProduct.coeff 5 =
      (
        (-757660479951474023544) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_6 :
    recurrence5ExceptionalProduct.coeff 6 =
      (
        (100811442218396807528901) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_7 :
    recurrence5ExceptionalProduct.coeff 7 =
      (
        (-216764707546917918400108899) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_8 :
    recurrence5ExceptionalProduct.coeff 8 =
      (
        (95495346064655177619134458092) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_9 :
    recurrence5ExceptionalProduct.coeff 9 =
      (
        (-44281906534390794592551550682547) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_10 :
    recurrence5ExceptionalProduct.coeff 10 =
      (
        (10967929619401068925101522942152989) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_11 :
    recurrence5ExceptionalProduct.coeff 11 =
      (
        (2484947366860568066558377249168286173) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_12 :
    recurrence5ExceptionalProduct.coeff 12 =
      (
        (-672157926834138083152541117755014737377) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_13 :
    recurrence5ExceptionalProduct.coeff 13 =
      (
        (1701587270010574181692603308869611655525787) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_14 :
    recurrence5ExceptionalProduct.coeff 14 =
      (
        (-720713764665413256306774644524750039413889581) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_15 :
    recurrence5ExceptionalProduct.coeff 15 =
      (
        (286188480808271394191025734265558907735908882327) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_16 :
    recurrence5ExceptionalProduct.coeff 16 =
      (
        (-341216970672754366711484605520784548273527198290283) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_17 :
    recurrence5ExceptionalProduct.coeff 17 =
      (
        (7537520771005310288606618176512833522864829455375737) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_18 :
    recurrence5ExceptionalProduct.coeff 18 =
      (
        (2483405824670484450387683378206564621668576571238922763) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_19 :
    recurrence5ExceptionalProduct.coeff 19 =
      (
        (-3515672202850547814231659251805578922042140555019610392487) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_20 :
    recurrence5ExceptionalProduct.coeff 20 =
      (
        (3210486136458743345145907760361455634881980096743705840497163) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_21 :
    recurrence5ExceptionalProduct.coeff 21 =
      (
        (-1639444519904797583700262616242561051511534422058942516951669919) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_22 :
    recurrence5ExceptionalProduct.coeff 22 =
      (
        (312995508141412692485729371046931428396176100830209661062210852227) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_23 :
    recurrence5ExceptionalProduct.coeff 23 =
      (
        (-11194376494643205154179431406668642659061147481165621813589021262238) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_24 :
    recurrence5ExceptionalProduct.coeff 24 =
      (
        (1115915329431096721051854246172964277120855960574732934811205212133424) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_25 :
    recurrence5ExceptionalProduct.coeff 25 =
      (
        -((10 * 10 ^ 70 +
          0253958156800182111401985643880535363610882812548305461669946749750601)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_26 :
    recurrence5ExceptionalProduct.coeff 26 =
      (
        -((1377 * 10 ^ 70 +
          6461180711763626525935582704926844123309087307259002391943237101222757)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_27 :
    recurrence5ExceptionalProduct.coeff 27 =
      (
        ((199956 * 10 ^ 70 +
          7468455429016150215996631497748164575415039542879812428660855057132629)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_28 :
    recurrence5ExceptionalProduct.coeff 28 =
      (
        -((111239340 * 10 ^ 70 +
          2724111859608073617068967008488595121797207772595282251662855136038593)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_29 :
    recurrence5ExceptionalProduct.coeff 29 =
      (
        ((10467897569 * 10 ^ 70 +
          7701827627767381167257469079954599847167972019220805010949792072903083)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_30 :
    recurrence5ExceptionalProduct.coeff 30 =
      (
        -((642326081315 * 10 ^ 70 +
          3466475752910898145658657408991106403523206553631334052634323188262039)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_31 :
    recurrence5ExceptionalProduct.coeff 31 =
      (
        ((2639400027316 * 10 ^ 70 +
          7676175966813188446325926210127874842579925460685929715215899261493829)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_32 :
    recurrence5ExceptionalProduct.coeff 32 =
      (
        ((3340833767518486 * 10 ^ 70 +
          5437737741824380825697072841981873716471788345619632405473844930745987)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_33 :
    recurrence5ExceptionalProduct.coeff 33 =
      (
        -((551827683050119992 * 10 ^ 70 +
          4698680028085395255688626250620851770885284221246339540279782733702313)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_34 :
    recurrence5ExceptionalProduct.coeff 34 =
      (
        ((27833519513960707822 * 10 ^ 70 +
          8654136362060708346420733750456686124529574428785688027732450526885283)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_35 :
    recurrence5ExceptionalProduct.coeff 35 =
      (
        -((4366133600967097174014 * 10 ^ 70 +
          7128861775850674459970086430816269759864053526515129849483833911779157)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_36 :
    recurrence5ExceptionalProduct.coeff 36 =
      (
        ((71333511044627941720496 * 10 ^ 70 +
          1947709151868042484908510537306559959274851128857308010292130829266414)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_37 :
    recurrence5ExceptionalProduct.coeff 37 =
      (
        -((16013559129984398637472399 * 10 ^ 70 +
          8929107772752755678600455487667935591175073012431501853788703992973657)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_38 :
    recurrence5ExceptionalProduct.coeff 38 =
      (
        ((196000200866387251113176623 * 10 ^ 70 +
          4931384419600674242565239964209417182940338835550197825311638425675692)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_39 :
    recurrence5ExceptionalProduct.coeff 39 =
      (
        -((33769795227773828675172256735 * 10 ^ 70 +
          6837020672256996176558672001749555851875748472758654645076324022830403)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_40 :
    recurrence5ExceptionalProduct.coeff 40 =
      (
        ((642366237811179911980600625305 * 10 ^ 70 +
          3477852655371701491769275785687879025118362437691477066801866685318011)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_41 :
    recurrence5ExceptionalProduct.coeff 41 =
      (
        -((43167848574387109436835485848926 * 10 ^ 70 +
          2839382503493463112281176310155993646389791048733549566847624383717567)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_42 :
    recurrence5ExceptionalProduct.coeff 42 =
      (
        ((1275251918254256437592350418002992 * 10 ^ 70 +
          3887220407759836487082039831201038920065498346296271944708714097709529)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_43 :
    recurrence5ExceptionalProduct.coeff 43 =
      (
        -((3274143182062757387199855382390438 * 10 ^ 70 +
          5544455019681879339543347524041891978008550102796076227228502838858441)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_44 :
    recurrence5ExceptionalProduct.coeff 44 =
      (
        ((712072388066374045990035371837780594 * 10 ^ 70 +
          4414847116755858549309743101467302611342919798564518778161859418446317)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_45 :
    recurrence5ExceptionalProduct.coeff 45 =
      (
        -((12311961000299184924502760495591891762 * 10 ^ 70 +
          4660590671804475563069220923937059112722315142290727806334174042274289)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_46 :
    recurrence5ExceptionalProduct.coeff 46 =
      (
        ((67326242419069438721812608529109506894 * 10 ^ 70 +
          0168201205314636618731271963221122157067665970785342262719283045770467)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_47 :
    recurrence5ExceptionalProduct.coeff 47 =
      (
        ((688984313580539274241097730204344028803 * 10 ^ 70 +
          6596833593337978486697369511255643848446956848339164197209915976013993)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_48 :
    recurrence5ExceptionalProduct.coeff 48 =
      (
        -((87189841479161244182432998438696482400002 * 10 ^ 70 +
          4178522696175498584191159850741557770987316217568835258346529484215717)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_49 :
    recurrence5ExceptionalProduct.coeff 49 =
      (
        ((1439052114363604111266891803251637115695304 * 10 ^ 70 +
          1134218146536914211655013059543581813035740158874658368260464400580759)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5ExceptionalProduct_coeff_50 :
    recurrence5ExceptionalProduct.coeff 50 =
      (
        -((66337881643071834499947585918076605277262248 * 10 ^ 70 +
          6996676748543308614581867338343161535794134481519370718304214831627473)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_51_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5A3Square.coeff x * exceptional5.coeff (51 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (51 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_51 :
    recurrence5ExceptionalProduct.coeff 51 =
      (
        ((236123742568945300279956624657620538838107356 * 10 ^ 70 +
          8000950671263247984282327827647739809402046579313465027246668609436363)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 52 = 1 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_51_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_52_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5A3Square.coeff x * exceptional5.coeff (52 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (52 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_52 :
    recurrence5ExceptionalProduct.coeff 52 =
      (
        -((3151674734441543116853239968977448643904651280 * 10 ^ 70 +
          4844562933130133417346755618121299188902776692530264942577425320343163)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 53 = 2 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_52_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_53_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5A3Square.coeff x * exceptional5.coeff (53 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (53 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_53 :
    recurrence5ExceptionalProduct.coeff 53 =
      (
        ((30178572147810206332405553410014788974166500820 * 10 ^ 70 +
          2317405335247710505388401593955862227463162117024434831903576556476428)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 54 = 3 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_53_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_54_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5A3Square.coeff x * exceptional5.coeff (54 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (54 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_54 :
    recurrence5ExceptionalProduct.coeff 54 =
      (
        ((477728874072814469611577410184956808023060082368 * 10 ^ 70 +
          5804068664598089361866267107780500251306620500592201993846595308690563)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 55 = 4 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_54_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_55_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5A3Square.coeff x * exceptional5.coeff (55 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (55 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_55 :
    recurrence5ExceptionalProduct.coeff 55 =
      (
        -((15030148142482545563836355958725197898600368813632 * 10 ^ 70 +
          3672366637158744267588178509440760169281323733380101026759056116611513)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 56 = 5 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_55_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_56_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5A3Square.coeff x * exceptional5.coeff (56 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (56 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_56 :
    recurrence5ExceptionalProduct.coeff 56 =
      (
        ((719785021663688856057343293571593349762431441083292 * 10 ^ 70 +
          4775521950558910469834561657711589158698286522979969849729421382979363)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 57 = 6 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_56_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_57_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5A3Square.coeff x * exceptional5.coeff (57 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (57 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_57 :
    recurrence5ExceptionalProduct.coeff 57 =
      (
        -((1246128356304360061703609575122444317287267153490411 * 10 ^ 70 +
          1913663663745150329807913999977392033503237008920873673125122472957019)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 58 = 7 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_57_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_58_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5A3Square.coeff x * exceptional5.coeff (58 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (58 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_58 :
    recurrence5ExceptionalProduct.coeff 58 =
      (
        ((342185171704930423738779575542383938356084482649010104 * 10 ^ 70 +
          5195364968932544271861471709281124081358453160401304244362264221142149)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 59 = 8 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_58_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_59_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5A3Square.coeff x * exceptional5.coeff (59 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (59 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_59 :
    recurrence5ExceptionalProduct.coeff 59 =
      (
        -((3726951221326008625728762687324449253680086287347386572 * 10 ^ 70 +
          5363819824453014016858982797073503437489645199472250774295349823238989)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 60 = 9 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_59_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_60_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5A3Square.coeff x * exceptional5.coeff (60 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (60 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_60 :
    recurrence5ExceptionalProduct.coeff 60 =
      (
        ((14726043727350114600620118414143776831635360103916011853 * 10 ^ 70 +
          3938264456847774885805683451645962364487029592078616476878917411923373)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 61 = 10 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_60_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_61_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5A3Square.coeff x * exceptional5.coeff (61 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (61 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_61 :
    recurrence5ExceptionalProduct.coeff 61 =
      (
        -((94456238927833850775454944354911622070808671644738104848 * 10 ^ 70 +
          6367018838453974741908699794790233288112704710186100148769817392901079)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 62 = 11 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_61_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_62_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5A3Square.coeff x * exceptional5.coeff (62 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (62 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_62 :
    recurrence5ExceptionalProduct.coeff 62 =
      (
        -((92857454132625853770328827704137241694512253451338159087 * 10 ^ 70 +
          6398032669243347607298608379701521169021634206182896401416588800077383)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 63 = 12 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_62_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_63_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5A3Square.coeff x * exceptional5.coeff (63 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (63 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_63 :
    recurrence5ExceptionalProduct.coeff 63 =
      (
        ((9048773948280954230738232019709743059968373220711940754450 * 10 ^ 70 +
          8564566053921289129858455341314405129006964011266534288979680720950003)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 64 = 13 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_63_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_64_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5A3Square.coeff x * exceptional5.coeff (64 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (64 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_64 :
    recurrence5ExceptionalProduct.coeff 64 =
      (
        -((148916960806431178392379307983204069177036628845507600118873 * 10 ^ 70 +
          4571857441127299009163312798195667640046623820614094343096628935762233)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 65 = 14 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_64_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_65_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5A3Square.coeff x * exceptional5.coeff (65 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (65 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_65 :
    recurrence5ExceptionalProduct.coeff 65 =
      (
        ((5428543190162069163850485584498760862554345228846639717828330 * 10 ^ 70 +
          3678929676553524193255465147058749138797751692124156658607170472593383)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 66 = 15 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_65_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_66_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5A3Square.coeff x * exceptional5.coeff (66 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (66 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_66 :
    recurrence5ExceptionalProduct.coeff 66 =
      (
        -((816653856665545146027637429221563825631887341637647482295377 * 10 ^ 70 +
          0487680631222793532687674677833490814465699200408747864686420460000403)) /
        (738070452448895892793300 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 67 = 16 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_66_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_67_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5A3Square.coeff x * exceptional5.coeff (67 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (67 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_67 :
    recurrence5ExceptionalProduct.coeff 67 =
      (
        -((16647655709820557812710397978409700064551081413431242577399185 * 10 ^ 70 +
          5879778343120535098383276644742241811459918725060061927103340562563911)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 68 = 17 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_67_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_68_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5A3Square.coeff x * exceptional5.coeff (68 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (68 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_68 :
    recurrence5ExceptionalProduct.coeff 68 =
      (
        ((818045639452742509487822340910899837505300518709108958951621439 * 10 ^ 70 +
          4291752318718456703764792129029547087098656154847934843855333983065449)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 69 = 18 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_68_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_69_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5A3Square.coeff x * exceptional5.coeff (69 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (69 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_69 :
    recurrence5ExceptionalProduct.coeff 69 =
      (
        -((23324860856202143915675919647631884231064736424535689655363650832 * 10 ^ 70 +
          4135386943792353792236030414983132849962581090597294944337774232097619)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 70 = 19 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_69_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_70_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5A3Square.coeff x * exceptional5.coeff (70 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (70 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_70 :
    recurrence5ExceptionalProduct.coeff 70 =
      (
        ((414643162383539002624812033051553975840929313993006361820263925270 * 10 ^ 70 +
          4605200627427092425653361141724811825775064019147155141290456007133979)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 71 = 20 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_70_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_71_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5A3Square.coeff x * exceptional5.coeff (71 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (71 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_71 :
    recurrence5ExceptionalProduct.coeff 71 =
      (
        -((2225971920530168787351535430173208295912080747969959060401937227949 * 10 ^ 70 +
          9544375581753079106222545365247425855597903632874365827584388457131477)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 72 = 21 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_71_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_72_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5A3Square.coeff x * exceptional5.coeff (72 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (72 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_72 :
    recurrence5ExceptionalProduct.coeff 72 =
      (
        -((30780824081329347751806893320766653085278971058542512273047380911 * 10 ^ 70 +
          7460609746523755121141415924082749688487709589711882788863529399533299)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 73 = 22 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_72_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_73_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5A3Square.coeff x * exceptional5.coeff (73 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (73 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_73 :
    recurrence5ExceptionalProduct.coeff 73 =
      (
        ((172329760941705495006504953951705551625582184750271152906692320942603 * 10 ^ 70 +
          0665928152601537507387250179283900814481096266513183717659297627646511)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 74 = 23 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_73_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_74_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5A3Square.coeff x * exceptional5.coeff (74 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (74 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_74 :
    recurrence5ExceptionalProduct.coeff 74 =
      (
        -((61058061802981623029376606806443202366894773710420183549367077429708 * 10 ^ 70 +
          7834852662939162117904246127173471259667675610847221789132433459542517)) /
        (738070452448895892793300 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 75 = 24 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_74_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_75_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5A3Square.coeff x * exceptional5.coeff (75 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (75 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_75 :
    recurrence5ExceptionalProduct.coeff 75 =
      (
        ((1778708839938916102908032048117745991890808972182893258924457206495056 * 10 ^ 70 +
          2041878902067948824433241936223947153647542221990520457521491726956337)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 76 = 25 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_75_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_76_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5A3Square.coeff x * exceptional5.coeff (76 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (76 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_76 :
    recurrence5ExceptionalProduct.coeff 76 =
      (
        -(((1 * 10 ^ 70 +
          9837180590798157475279001311109115849265341973362915958537680678591076) * 10 ^ 70 +
          4878356355618900429834707097978680394633967648012920470951119886599374)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 77 = 26 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_76_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_77_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5A3Square.coeff x * exceptional5.coeff (77 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (77 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_77 :
    recurrence5ExceptionalProduct.coeff 77 =
      (
        -(((6 * 10 ^ 70 +
          5193802811782163788090483663463793449505202138940830704956427715819689) * 10 ^ 70 +
          9758846121239654386206048828084053124681637673237648901857302016852647)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 78 = 27 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_77_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_78_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5A3Square.coeff x * exceptional5.coeff (78 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (78 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_78 :
    recurrence5ExceptionalProduct.coeff 78 =
      (
        (((644 * 10 ^ 70 +
          5099057097564484374282158178602067979570377982438354264178025609008049) * 10 ^ 70 +
          2719587010204688785863953611968404396869462710732262481445337190185517)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 79 = 28 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_78_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_79_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5A3Square.coeff x * exceptional5.coeff (79 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (79 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_79 :
    recurrence5ExceptionalProduct.coeff 79 =
      (
        -(((7005 * 10 ^ 70 +
          6376908543753043975363537759224337549132769127395601501261309589286079) * 10 ^ 70 +
          6946617225435735341926834373463447147538926667794048284431250915733619)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 80 = 29 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_79_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_80_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5A3Square.coeff x * exceptional5.coeff (80 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (80 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_80 :
    recurrence5ExceptionalProduct.coeff 80 =
      (
        (((46284 * 10 ^ 70 +
          3490105745422554948159890967789743272550460840557426141078582071448968) * 10 ^ 70 +
          4163233575266387065216490618722237055604413976728729158097424568322071)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 81 = 30 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_80_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_81_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5A3Square.coeff x * exceptional5.coeff (81 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (81 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_81 :
    recurrence5ExceptionalProduct.coeff 81 =
      (
        -(((7654 * 10 ^ 70 +
          3692752452407220459424048088083333136899117546851607689964791940653614) * 10 ^ 70 +
          9750386254254958721245635185486135909300227673253077493491538147243689)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 82 = 31 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_81_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_82_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5A3Square.coeff x * exceptional5.coeff (82 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (82 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_82 :
    recurrence5ExceptionalProduct.coeff 82 =
      (
        -(((178085 * 10 ^ 70 +
          9051382360284165193755616043423068051525156418685257486097695719862999) * 10 ^ 70 +
          4205803297139688834889439582818191011898200755153621219641451451210643)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 83 = 32 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_82_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_83_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5A3Square.coeff x * exceptional5.coeff (83 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (83 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_83 :
    recurrence5ExceptionalProduct.coeff 83 =
      (
        (((3975951 * 10 ^ 70 +
          8590870198073581983619371736998167468836634366648150516762632031016955) * 10 ^ 70 +
          6515193944283061941254697638008196646474407392295804676263198301131648)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 84 = 33 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_83_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_84_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5A3Square.coeff x * exceptional5.coeff (84 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (84 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_84 :
    recurrence5ExceptionalProduct.coeff 84 =
      (
        -(((28122830 * 10 ^ 70 +
          1489812627627179315233347101555577832167588953700574236929691511828507) * 10 ^ 70 +
          7532815426146296943822105341667984832972027087886110982850127402201043)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 85 = 34 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_84_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_85_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5A3Square.coeff x * exceptional5.coeff (85 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (85 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_85 :
    recurrence5ExceptionalProduct.coeff 85 =
      (
        (((764823238 * 10 ^ 70 +
          6804381021887996823426247651921951270121213684184374730229050658407924) * 10 ^ 70 +
          1344111137183728699668947490170924894632747890613065488533781077701007)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 86 = 35 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_85_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_86_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5A3Square.coeff x * exceptional5.coeff (86 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (86 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_86 :
    recurrence5ExceptionalProduct.coeff 86 =
      (
        -(((1627845985 * 10 ^ 70 +
          1173710268770304824726060826989640801622609950563761302649818997968007) * 10 ^ 70 +
          1401252930620238539738601393956566985655385966000146680345137053699531)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 87 = 36 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_86_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_87_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5A3Square.coeff x * exceptional5.coeff (87 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (87 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_87 :
    recurrence5ExceptionalProduct.coeff 87 =
      (
        -(((8768178196 * 10 ^ 70 +
          7722557031065684878362461051053064713297271643037024941892277294272641) * 10 ^ 70 +
          3138844380416990478610924830953883056595351804095628664555314997665739)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 88 = 37 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_87_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_88_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5A3Square.coeff x * exceptional5.coeff (88 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (88 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_88 :
    recurrence5ExceptionalProduct.coeff 88 =
      (
        (((25509936193 * 10 ^ 70 +
          1073168369784778220075430514062115329683837552962499211236433826264805) * 10 ^ 70 +
          0546774438948154430396133769796679053854072194676023462633462405112759)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 89 = 38 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_88_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_89_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5A3Square.coeff x * exceptional5.coeff (89 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (89 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_89 :
    recurrence5ExceptionalProduct.coeff 89 =
      (
        -(((939302486547 * 10 ^ 70 +
          2862585113892399016955282960585239761217878336297790784258890069813968) * 10 ^ 70 +
          1184328404349971041475978849984762074234472812619782838360558620075189)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 90 = 39 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_89_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_90_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5A3Square.coeff x * exceptional5.coeff (90 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (90 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_90 :
    recurrence5ExceptionalProduct.coeff 90 =
      (
        (((2124659060123 * 10 ^ 70 +
          1182760516847907168868020534295746359727599411339634584564876287279751) * 10 ^ 70 +
          0240952626263668569204369536072684305576241796283393364860836124279084)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 91 = 40 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_90_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_91_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5A3Square.coeff x * exceptional5.coeff (91 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (91 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_91 :
    recurrence5ExceptionalProduct.coeff 91 =
      (
        -(((2350089329382 * 10 ^ 70 +
          8565067276031574718597778459261647584176407316394164985322266616278324) * 10 ^ 70 +
          4385115062203979196456743164209821088717898696219588409776505338824684)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 92 = 41 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_91_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_92_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5A3Square.coeff x * exceptional5.coeff (92 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (92 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_92 :
    recurrence5ExceptionalProduct.coeff 92 =
      (
        -(((241026563679622 * 10 ^ 70 +
          5958726634412038025091525216101667531254059430270385615919767994701620) * 10 ^ 70 +
          3285500841855303399344242859641080945966747101607957893194119955484813)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 93 = 42 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_92_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_93_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5A3Square.coeff x * exceptional5.coeff (93 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (93 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_93 :
    recurrence5ExceptionalProduct.coeff 93 =
      (
        (((2724934101612359 * 10 ^ 70 +
          3790004334958734435193212856052689647736305596646411230137205944859861) * 10 ^ 70 +
          3812962680931326945769958711246349473295723863059785675373118597610569)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 94 = 43 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_93_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_94_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5A3Square.coeff x * exceptional5.coeff (94 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (94 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_94 :
    recurrence5ExceptionalProduct.coeff 94 =
      (
        -(((1746076519884076 * 10 ^ 70 +
          0113255214818700153674737708757783233660839903890751031771608516136439) * 10 ^ 70 +
          7723456652032406063884262211716483200353084362654222500788046268075943)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 95 = 44 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_94_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_95_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5A3Square.coeff x * exceptional5.coeff (95 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (95 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_95 :
    recurrence5ExceptionalProduct.coeff 95 =
      (
        (((68755196794785988 * 10 ^ 70 +
          3465864266623056512001851928330808700494405435376880712464105095024833) * 10 ^ 70 +
          8188973613552450456346038725820463548355775485342427550828149736122327)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 96 = 45 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_95_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_96_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5A3Square.coeff x * exceptional5.coeff (96 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (96 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_96 :
    recurrence5ExceptionalProduct.coeff 96 =
      (
        -(((7258393959950877 * 10 ^ 70 +
          7683303680221360734243095871053861203913146602440110303582370399066474) * 10 ^ 70 +
          2948780153584346125082727853129290093371311355911545217285082543567883)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 97 = 46 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_96_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5A3Square.coeff x * exceptional5.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (97 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_97 :
    recurrence5ExceptionalProduct.coeff 97 =
      (
        -(((1011636514831839080 * 10 ^ 70 +
          4495965747969727352169601978963626387769347081465232737440801061128052) * 10 ^ 70 +
          1101969070571869656873865556745685559453481913599993346813557383143429)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 98 = 47 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_97_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5A3Square.coeff x * exceptional5.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (98 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_98 :
    recurrence5ExceptionalProduct.coeff 98 =
      (
        (((20030488164978365597 * 10 ^ 70 +
          8872876037861068734488274769834184277663628527186227900381569147337975) * 10 ^ 70 +
          7123129868227861367381005554088694551887277934398128788290052235276111)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 99 = 48 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_98_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5A3Square.coeff x * exceptional5.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (99 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_99 :
    recurrence5ExceptionalProduct.coeff 99 =
      (
        -(((118355760192962991688 * 10 ^ 70 +
          5950216187306881779285411726079925125265277286296090253218464129821425) * 10 ^ 70 +
          3743916387862324677485615473656459184219985814179501152776868354198013)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 100 = 49 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_99_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5A3Square.coeff x * exceptional5.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (100 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_100 :
    recurrence5ExceptionalProduct.coeff 100 =
      (
        (((441510381007962393947 * 10 ^ 70 +
          8993232852193886167442333806259756975240600738105764119500538413625522) * 10 ^ 70 +
          1752813006978764806184857398955295215843042568977011280425923308674939)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 101 = 50 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_100_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5A3Square.coeff x * exceptional5.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (101 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_101 :
    recurrence5ExceptionalProduct.coeff 101 =
      (
        -(((78216028095205055251 * 10 ^ 70 +
          1351996493142303342887549687242996722042529303493754020801899356827073) * 10 ^ 70 +
          1463189579059450328239410158338826248759119610430937470707262944911801)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 102 = 51 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_101_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5A3Square.coeff x * exceptional5.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (102 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_102 :
    recurrence5ExceptionalProduct.coeff 102 =
      (
        -(((10579791269985137790404 * 10 ^ 70 +
          2287932797678695517496756475068909190600962003546581237610791794101552) * 10 ^ 70 +
          7401600494174566644467757952903393219808418628808504112163780634387869)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 103 = 52 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_102_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5A3Square.coeff x * exceptional5.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_103 :
    recurrence5ExceptionalProduct.coeff 103 =
      (
        (((103164420494194124178234 * 10 ^ 70 +
          7986132897983130276199638621483861370920922959905639081026252540325749) * 10 ^ 70 +
          8747587338372123037442974378225508930691246583020421054685352891221313)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 104 = 53 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5A3Square.coeff x * exceptional5.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_104 :
    recurrence5ExceptionalProduct.coeff 104 =
      (
        -(((602436672643220616364549 * 10 ^ 70 +
          2036089570589375327947097615191083224207195076708458430309591390048071) * 10 ^ 70 +
          2583972417979766454526514299613113970515053015001354296725098371922767)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 105 = 54 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5A3Square.coeff x * exceptional5.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_105 :
    recurrence5ExceptionalProduct.coeff 105 =
      (
        (((1174618963194422695524479 * 10 ^ 70 +
          4277028161636843056107902187602110575025376849557848330627456697697352) * 10 ^ 70 +
          7858269648537143040955516106035640572037534389384512483158295674648769)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 106 = 55 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5A3Square.coeff x * exceptional5.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_106 :
    recurrence5ExceptionalProduct.coeff 106 =
      (
        -(((3748433146775850138570644 * 10 ^ 70 +
          1529938053360823755072520203452046112530464219415998500525421338315468) * 10 ^ 70 +
          1081889004403142689223698613186958734274901480511230743263340698782771)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 107 = 56 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5A3Square.coeff x * exceptional5.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_107 :
    recurrence5ExceptionalProduct.coeff 107 =
      (
        -(((31002333763990925093458302 * 10 ^ 70 +
          2984738683389113864455524492889712681671828745007913437457041390523676) * 10 ^ 70 +
          8514215402641863669153623703830149838462231730348185340203269021310407)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 108 = 57 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5A3Square.coeff x * exceptional5.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_108 :
    recurrence5ExceptionalProduct.coeff 108 =
      (
        (((181381614439481968809755884 * 10 ^ 70 +
          7468842117133497990601178120361827653214323173999180834846023364506684) * 10 ^ 70 +
          5892270565399507780105583183380532229997958481259283621328543474015489)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 109 = 58 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5A3Square.coeff x * exceptional5.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_109 :
    recurrence5ExceptionalProduct.coeff 109 =
      (
        -(((454435353822923714050332420 * 10 ^ 70 +
          5341593948547138040825801111064382915946425839689633258958687437533422) * 10 ^ 70 +
          4615304869212445082118636136461198478238338592314731811102278812635189)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 110 = 59 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5A3Square.coeff x * exceptional5.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_110 :
    recurrence5ExceptionalProduct.coeff 110 =
      (
        (((1993927799133381581979132791 * 10 ^ 70 +
          7835001750868585540514915510409212650536055042544201026570828418747923) * 10 ^ 70 +
          2896851019568251130447848055686725328628606204098732790317152657527187)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 111 = 60 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5A3Square.coeff x * exceptional5.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_111 :
    recurrence5ExceptionalProduct.coeff 111 =
      (
        -(((6831771612962526212707374511 * 10 ^ 70 +
          1876467585455529832804620032095610002160126935590712084231989193097115) * 10 ^ 70 +
          9485507035275147742932198423530344148296434074562536809654703097565311)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 112 = 61 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5A3Square.coeff x * exceptional5.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_112 :
    recurrence5ExceptionalProduct.coeff 112 =
      (
        -(((13151539395374226813519856796 * 10 ^ 70 +
          5188936442831033208244369171500089045105994108708574862797818770733923) * 10 ^ 70 +
          7370916959969225476042992214460653275259524264800840210844271318957447)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 62 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5A3Square.coeff x * exceptional5.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_113 :
    recurrence5ExceptionalProduct.coeff 113 =
      (
        (((749962343399969674482040969032 * 10 ^ 70 +
          2718186247755655702816471587691554356705455097849119962370009989981099) * 10 ^ 70 +
          1321481668385642168099519195888904376768478563220805425299230244159341)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 63 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5A3Square.coeff x * exceptional5.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_114 :
    recurrence5ExceptionalProduct.coeff 114 =
      (
        -(((1455880046652144405829588360011 * 10 ^ 70 +
          1784609401338548304107185420262340576489713656370622030275888624943037) * 10 ^ 70 +
          8227409952298395397635287670824933266313799040657154715841216273992443)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 64 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5A3Square.coeff x * exceptional5.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_115 :
    recurrence5ExceptionalProduct.coeff 115 =
      (
        (((30397425965435677964621296877866 * 10 ^ 70 +
          3741307842904521191182045767496126210883077961162578402005185924243585) * 10 ^ 70 +
          5845614951379117332805105708504389992093095459704487522531933505815789)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 65 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence5A3Square.coeff x * exceptional5.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_116 :
    recurrence5ExceptionalProduct.coeff 116 =
      (
        -(((29247300461468840510450361019630 * 10 ^ 70 +
          1829368779062152481200807469244596475395503068710705894354359064028043) * 10 ^ 70 +
          9115337106561164404980244924247794583732972542223260911726823387290221)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 66 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence5A3Square.coeff x * exceptional5.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_117 :
    recurrence5ExceptionalProduct.coeff 117 =
      (
        (((56590283438826424757581796679692 * 10 ^ 70 +
          9994547242442366014222924822243802466431551110703623013745293719301897) * 10 ^ 70 +
          6121098693795178190216329266075298031450815108939468430872575920557669)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 67 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence5A3Square.coeff x * exceptional5.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_118 :
    recurrence5ExceptionalProduct.coeff 118 =
      (
        (((106073662999367427537026835908540 * 10 ^ 70 +
          5713487284436307612552257155990015848448341440050133608985092412365897) * 10 ^ 70 +
          2466392027187346874304777179386098353878652854675955783004044664884119)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 68 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence5A3Square.coeff x * exceptional5.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_119 :
    recurrence5ExceptionalProduct.coeff 119 =
      (
        -(((7517507360565647176062753307838224 * 10 ^ 70 +
          3638189701876969028189597628883486581514500692622745433264640223402231) * 10 ^ 70 +
          1993605221807666731943968238792076305809152652933204202698412763173509)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 69 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence5A3Square.coeff x * exceptional5.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_120 :
    recurrence5ExceptionalProduct.coeff 120 =
      (
        (((10975872586147674391686930623664955 * 10 ^ 70 +
          6075859377152708436105135840968626505770575784180323896485475202189072) * 10 ^ 70 +
          7810101042304110016030924380793141363384332465017338793512366693974307)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 70 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence5A3Square.coeff x * exceptional5.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_121 :
    recurrence5ExceptionalProduct.coeff 121 =
      (
        -(((140366715736810695826383752792861516 * 10 ^ 70 +
          8311119172882754285204974966387025526163408498396836403297869538855794) * 10 ^ 70 +
          9982857445602756806407054251433098779769393137080059098157071253303497)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 71 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence5A3Square.coeff x * exceptional5.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_122 :
    recurrence5ExceptionalProduct.coeff 122 =
      (
        (((280323465116698575709917872760448180 * 10 ^ 70 +
          0185798442353901071441113148038249465509280721499600426513473160715961) * 10 ^ 70 +
          0662936886291632516595739123739121753722327288419768465176390386679048)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 72 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence5A3Square.coeff x * exceptional5.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_123 :
    recurrence5ExceptionalProduct.coeff 123 =
      (
        -(((837574785147661405263031789398476136 * 10 ^ 70 +
          7871221400170272532735766013850495522190627924551617492919067261912994) * 10 ^ 70 +
          0083622991254618633219531202249356601779188595473272164933720674682607)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 73 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence5A3Square.coeff x * exceptional5.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_124 :
    recurrence5ExceptionalProduct.coeff 124 =
      (
        (((66832006643177995615329031785043307 * 10 ^ 70 +
          9057369831201862384991483827831323594744487032563070345225637215226234) * 10 ^ 70 +
          7060092065612296949263242315817421572800984173454999123749491567207451)) /
        (369035226224447946396650 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 74 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence5A3Square.coeff x * exceptional5.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_125 :
    recurrence5ExceptionalProduct.coeff 125 =
      (
        (((11569281872160970249074640380197256036 * 10 ^ 70 +
          5250689080062210076138501720907840762797425709559111648063300510481879) * 10 ^ 70 +
          6277320230795794584052620286648363982113301928845564248793103172395951)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 75 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence5A3Square.coeff x * exceptional5.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_126 :
    recurrence5ExceptionalProduct.coeff 126 =
      (
        -(((66113966084409414706645115570493125746 * 10 ^ 70 +
          5310628932270509486468870687849288911284387553639589196347331942220838) * 10 ^ 70 +
          9140689176279358848921660035877263588512961688197980802169400796636098)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 76 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence5A3Square.coeff x * exceptional5.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_127 :
    recurrence5ExceptionalProduct.coeff 127 =
      (
        (((79976535847962217535631029418136766034 * 10 ^ 70 +
          4454513310558720413700602429516394970113417388594834852388395879685823) * 10 ^ 70 +
          7114706857277466430624931269061107253743036017892317480691764148525912)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 77 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence5A3Square.coeff x * exceptional5.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_128 :
    recurrence5ExceptionalProduct.coeff 128 =
      (
        -(((7530911538172489904206935976039853405672 * 10 ^ 70 +
          2482492280967607680963986508677357984100902219514938792285431114737814) * 10 ^ 70 +
          5308580638790529626584026031977277328256150673702879658238212276974417)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 78 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence5A3Square.coeff x * exceptional5.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_129 :
    recurrence5ExceptionalProduct.coeff 129 =
      (
        (((29657981183012655845902605774414929439597 * 10 ^ 70 +
          7703203117886272404447030986628603749020334580667123892782113374556243) * 10 ^ 70 +
          2100905185559417350181572149685743904911447967919729918616402277444783)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 79 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence5A3Square.coeff x * exceptional5.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_130 :
    recurrence5ExceptionalProduct.coeff 130 =
      (
        -(((48790639132606723550109159710903270068128 * 10 ^ 70 +
          6473619201541655898052439524186608257723122340949829808162869804663321) * 10 ^ 70 +
          1580271075102520104778719843745198064001013739223943182278862830831787)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 80 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence5A3Square.coeff x * exceptional5.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_131 :
    recurrence5ExceptionalProduct.coeff 131 =
      (
        (((247079584262608396533202491246174147327715 * 10 ^ 70 +
          4797723442799236107923222379909373282634909414668273382156537065742220) * 10 ^ 70 +
          1137347358746685523979024412090785645229819570478493072828728583011343)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 81 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence5A3Square.coeff x * exceptional5.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_132 :
    recurrence5ExceptionalProduct.coeff 132 =
      (
        -(((285859196888028176280722107662587893320351 * 10 ^ 70 +
          0994790426632764272146296363484070233271591402168919982233364337927668) * 10 ^ 70 +
          9046728799856996977276322677091059167812773307365655911083747605773797)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 82 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence5A3Square.coeff x * exceptional5.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_133 :
    recurrence5ExceptionalProduct.coeff 133 =
      (
        -(((86083539636181585269624466669041399788593 * 10 ^ 70 +
          3407505827479760974142831521793488370099105854754379994318147230992965) * 10 ^ 70 +
          0803159795598463402257676270066452192107362843274856484145969664055406)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 83 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence5A3Square.coeff x * exceptional5.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_134 :
    recurrence5ExceptionalProduct.coeff 134 =
      (
        (((8480015418893767224474518794749540747099181 * 10 ^ 70 +
          7146073865681141527978156809201256538701649844930633844694013248819831) * 10 ^ 70 +
          5776755509860203617235483828155309165618943636005660343980037886684069)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 84 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence5A3Square.coeff x * exceptional5.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_135 :
    recurrence5ExceptionalProduct.coeff 135 =
      (
        -(((49077015700621991632613698067503718627940525 * 10 ^ 70 +
          4145786091507004373510140029802183452879647999431952299049481477899232) * 10 ^ 70 +
          4298221732077436504363791918121823131135597990995728614411999969538251)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 85 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence5A3Square.coeff x * exceptional5.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_136 :
    recurrence5ExceptionalProduct.coeff 136 =
      (
        (((465808660722656360029775121506090304906136260 * 10 ^ 70 +
          3092239154202711855487984944588993756212474325877562679838686877893491) * 10 ^ 70 +
          6753682675292017337267533082631138172903947463933754754740967330538021)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 86 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence5A3Square.coeff x * exceptional5.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_137 :
    recurrence5ExceptionalProduct.coeff 137 =
      (
        -(((1966575449816242274907135403999408503431724449 * 10 ^ 70 +
          5561991734786797645041496553622764682930218107808263781393474021886183) * 10 ^ 70 +
          9310904270427184030808068645880787021329642480469537863680927430162177)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 87 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence5A3Square.coeff x * exceptional5.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_138 :
    recurrence5ExceptionalProduct.coeff 138 =
      (
        (((381917838545865109085927230092444165515085340 * 10 ^ 70 +
          3536586494786214957045339866143367085522051402626812251220475381332021) * 10 ^ 70 +
          6035242141721271826128286820816150321606737542016275829680593455154683)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 88 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence5A3Square.coeff x * exceptional5.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_139 :
    recurrence5ExceptionalProduct.coeff 139 =
      (
        -(((27775610450808985680933142528192320067874154343 * 10 ^ 70 +
          0846627741181542551193861100424151411352459162123135041812371234753166) * 10 ^ 70 +
          0737109005783703007468379419919984215932615745880791203052024725769057)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 89 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence5A3Square.coeff x * exceptional5.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_140 :
    recurrence5ExceptionalProduct.coeff 140 =
      (
        (((95550663312350749396894892018960348734657763493 * 10 ^ 70 +
          2610364353979684375424811844966766487542629678295841960399832412376661) * 10 ^ 70 +
          9053358002697729854185087951831185201832120956056772402155173089749831)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 90 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence5A3Square.coeff x * exceptional5.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_141 :
    recurrence5ExceptionalProduct.coeff 141 =
      (
        -(((15654793858973566606671736650877807332941217739 * 10 ^ 70 +
          1937026385180917309156351266393936412124174397293847999673668136296453) * 10 ^ 70 +
          8293746195930952795718258944030280967723391311013391841392400731810208)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 91 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence5A3Square.coeff x * exceptional5.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_142 :
    recurrence5ExceptionalProduct.coeff 142 =
      (
        (((981902882969343212982511942582990813362966026380 * 10 ^ 70 +
          6409099335636986530156975498255583272809359799792890591664382069684541) * 10 ^ 70 +
          8461890139816887714630427905265950571346207868113051459474036530284297)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 92 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence5A3Square.coeff x * exceptional5.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_143 :
    recurrence5ExceptionalProduct.coeff 143 =
      (
        -(((2957532144241128813374444776434196097360708409874 * 10 ^ 70 +
          3454159480093984234290103231338760894380727067552811290061482427081604) * 10 ^ 70 +
          2176271800501678826568089373544396174609904422871345054961704938316081)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 93 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence5A3Square.coeff x * exceptional5.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_144 :
    recurrence5ExceptionalProduct.coeff 144 =
      (
        (((4289336560904017709841966701098241661756374234998 * 10 ^ 70 +
          2830007048933907171023649385897451029378682424436675138314652982046684) * 10 ^ 70 +
          9638345619935304873320411796625844344190214941052247050357551901521629)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 94 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence5A3Square.coeff x * exceptional5.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_145 :
    recurrence5ExceptionalProduct.coeff 145 =
      (
        -(((24013246373869666584886511047669951409948574202976 * 10 ^ 70 +
          1124435473263279826029363336518048449587649297876000349642308681013002) * 10 ^ 70 +
          6304650429779415563507911805275564073971206049460275308898240695422137)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 95 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence5A3Square.coeff x * exceptional5.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_146 :
    recurrence5ExceptionalProduct.coeff 146 =
      (
        (((32488028901496188918503711184129336046760013355878 * 10 ^ 70 +
          6113350552543419580261800556816371299834293193226545069697633926789480) * 10 ^ 70 +
          7240025424732193363221633298149689462385043979019217933381859221645981)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 96 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence5A3Square.coeff x * exceptional5.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_147 :
    recurrence5ExceptionalProduct.coeff 147 =
      (
        -(((170187181856000828102700468691101639677308966304486 * 10 ^ 70 +
          6943307308548274734675082332441865903733905166756574923649791694577520) * 10 ^ 70 +
          3025742714132661291441478967290459583624850422537650201239630982042207)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 97 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence5A3Square.coeff x * exceptional5.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_148 :
    recurrence5ExceptionalProduct.coeff 148 =
      (
        (((86397250759807533330010774781866108759105785289651 * 10 ^ 70 +
          3012773119529750208765260030328303774956701970983722507243914682136146) * 10 ^ 70 +
          5896403806471893039570517575165270893338959682646984919807977072545747)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 98 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence5A3Square.coeff x * exceptional5.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_149 :
    recurrence5ExceptionalProduct.coeff 149 =
      (
        -(((531829858233000555767488479693471527096202704940910 * 10 ^ 70 +
          1557637305402009827111247018445952573537199668095147798035632607663032) * 10 ^ 70 +
          6745932095812783984354533959295585783302676061342397401608156840824573)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 99 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence5A3Square.coeff x * exceptional5.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_150 :
    recurrence5ExceptionalProduct.coeff 150 =
      (
        (((1271314094870406785703014884980446210075450798498465 * 10 ^ 70 +
          1452566256816856966813644814622470961735556575612233574073363133317855) * 10 ^ 70 +
          3221031012018817731450248004093596523028551401964463860765286772521119)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 100 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence5A3Square.coeff x * exceptional5.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_151 :
    recurrence5ExceptionalProduct.coeff 151 =
      (
        -(((590496567161083581213945415583347794393424955674515 * 10 ^ 70 +
          9489282224970825405745702647783931893593373256951613574886989061067525) * 10 ^ 70 +
          6586128830177392879331504741515149163354297974502550490190671942383823)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 101 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence5A3Square.coeff x * exceptional5.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_152 :
    recurrence5ExceptionalProduct.coeff 152 =
      (
        (((13331269350963618133042095639988490488726862360257544 * 10 ^ 70 +
          3230630840236042487058644465585396874593488904346535106499509293306469) * 10 ^ 70 +
          6223364324297440895706930978905643883984909905485432403277625930982247)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 102 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence5A3Square.coeff x * exceptional5.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_153 :
    recurrence5ExceptionalProduct.coeff 153 =
      (
        -(((29273553989177639554023555945432168707758399125888199 * 10 ^ 70 +
          3608298811257476244192891153353739892672688672799321556792110113743476) * 10 ^ 70 +
          2275673410093483175538767768420134597591270918032947803169536096042599)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 103 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence5A3Square.coeff x * exceptional5.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_154 :
    recurrence5ExceptionalProduct.coeff 154 =
      (
        (((31275167814788014580976036870819660388659276254301607 * 10 ^ 70 +
          3734822147528516156247726918521209084863396572081573538903710155895768) * 10 ^ 70 +
          1314457624787848517403103934220939747461803924482660500096006994996541)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 104 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence5A3Square.coeff x * exceptional5.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_155 :
    recurrence5ExceptionalProduct.coeff 155 =
      (
        -(((26021886381007161971912421920719628677380488040493819 * 10 ^ 70 +
          9671454449162094057641224791486888026933976188628488415908034379172193) * 10 ^ 70 +
          9422787836998431023052843470791894502746728439234991344967002353686829)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 105 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5A3Square.coeff x * exceptional5.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_156 :
    recurrence5ExceptionalProduct.coeff 156 =
      (
        (((263551220152590582955654840306262363185024284111930520 * 10 ^ 70 +
          3414174481811693660705097460806973920784149609739427699573140053656245) * 10 ^ 70 +
          3885663671200402973828426908637073996466922390478991739914629088838923)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 106 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5A3Square.coeff x * exceptional5.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_157 :
    recurrence5ExceptionalProduct.coeff 157 =
      (
        -(((130008143596845764586613432659428537934378179326731221 * 10 ^ 70 +
          6936041492206329809627699774746231527159854153624567445007574533315601) * 10 ^ 70 +
          8458327447753503671675205029098935588825829238437306389930386810112699)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 107 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5A3Square.coeff x * exceptional5.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_158 :
    recurrence5ExceptionalProduct.coeff 158 =
      (
        (((249953625286963303816522452238756266366964335596603792 * 10 ^ 70 +
          9414761667173478450922796005022202311978064916187170631163051493138921) * 10 ^ 70 +
          3512892435617225937798298639775751360280592019182475091543377504424231)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 108 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5A3Square.coeff x * exceptional5.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_159 :
    recurrence5ExceptionalProduct.coeff 159 =
      (
        -(((93669726664990706078736464811072429340698983090274241 * 10 ^ 70 +
          2349898943949204016484272913724280558266287877849019824615632507715353) * 10 ^ 70 +
          1329571543807622471734441537179484175384346934801437376584926757614314)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 109 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5A3Square.coeff x * exceptional5.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_160 :
    recurrence5ExceptionalProduct.coeff 160 =
      (
        (((3421702018302135017726869831973993251527016255176290371 * 10 ^ 70 +
          4405498655970203875545660946851897038744571748371425689771997754574327) * 10 ^ 70 +
          5467400406614858839462006243161715848624629463006291944411066185170189)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 110 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5A3Square.coeff x * exceptional5.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_161 :
    recurrence5ExceptionalProduct.coeff 161 =
      (
        -(((6092925588623668215809833737908151987709316575101700711 * 10 ^ 70 +
          6663908807713847218666055480051108126311304090181517373786227881301921) * 10 ^ 70 +
          5776839311315031019825692096863970398495102672070015214797062214684619)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 111 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5A3Square.coeff x * exceptional5.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_162 :
    recurrence5ExceptionalProduct.coeff 162 =
      (
        (((528936978471590355456607642682313259014121901957567399 * 10 ^ 70 +
          8081279859861567803144421962568143570146040150922347134003742107792867) * 10 ^ 70 +
          0926424785657090792893540688263835288925954114708827015153436720028163)) /
        (1365430337030457401667605 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 112 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5A3Square.coeff x * exceptional5.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_163 :
    recurrence5ExceptionalProduct.coeff 163 =
      (
        -(((3582087539951390765220471575976362691323674691831614641 * 10 ^ 70 +
          1103735648839344050401598353388157243536703337166511699714569510031713) * 10 ^ 70 +
          6539303250367014205154959884007798613776343685571611386006077469086747)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 113 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5A3Square.coeff x * exceptional5.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_164 :
    recurrence5ExceptionalProduct.coeff 164 =
      (
        (((29571189855600637133272731220489457383486717901184378253 * 10 ^ 70 +
          6683733224294922716677040133630438677455257599106183257270703661979819) * 10 ^ 70 +
          4630576075366876430830125153290240492984368600995087597077625350778351)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 114 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5A3Square.coeff x * exceptional5.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_165 :
    recurrence5ExceptionalProduct.coeff 165 =
      (
        -(((11903476194977292952606220402648144376239480363407297222 * 10 ^ 70 +
          2169564486558637711386148240320573570448187347084081772883844987950409) * 10 ^ 70 +
          0210040078877537449997022453012865014055759660183747491678804788090402)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 115 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5A3Square.coeff x * exceptional5.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_166 :
    recurrence5ExceptionalProduct.coeff 166 =
      (
        (((74765056459692902610445509585314424797517591930095676675 * 10 ^ 70 +
          9449285321223221790491850621210163458458283270640895043133792070980318) * 10 ^ 70 +
          3617753461917709845179029689897612317636330039511626380359611069139459)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 116 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5A3Square.coeff x * exceptional5.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_167 :
    recurrence5ExceptionalProduct.coeff 167 =
      (
        -(((114484146960830040761784590000426160700253847519769218151 * 10 ^ 70 +
          4755306136721839280514529348801130060136375876962639416195216991797788) * 10 ^ 70 +
          5293245284709706064781511161950952971832110282338807686914072648392631)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 117 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5A3Square.coeff x * exceptional5.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_168 :
    recurrence5ExceptionalProduct.coeff 168 =
      (
        (((34187629675770153988611781184366101330116821268212279848 * 10 ^ 70 +
          0949314139829272036745755517793697649456722110134836871964770294651292) * 10 ^ 70 +
          4081874409615631018825044724771861613023063061858107954420650238340919)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 118 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5A3Square.coeff x * exceptional5.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_169 :
    recurrence5ExceptionalProduct.coeff 169 =
      (
        -(((124421700690908936450540684770825479311801455865947302352 * 10 ^ 70 +
          7186724168617404898587527209074533445191790018097577361610468077480183) * 10 ^ 70 +
          4700654839719789857874899743883843212990306916685047678945951941267027)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 119 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5A3Square.coeff x * exceptional5.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_170 :
    recurrence5ExceptionalProduct.coeff 170 =
      (
        (((176564060583295611604591346318625106725055219499825040330 * 10 ^ 70 +
          4311395446618950385148756435469563827994376123261116803808973539793133) * 10 ^ 70 +
          7450697376499682758376590821083131179744805037185951791978427560713403)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 120 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5A3Square.coeff x * exceptional5.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_171 :
    recurrence5ExceptionalProduct.coeff 171 =
      (
        -(((122095297299354422595413866811002513004141910232334714109 * 10 ^ 70 +
          2173954020130588154403437378640252392005803436981662526291412380356352) * 10 ^ 70 +
          8882722709217834684122577362160592486945399753427084683172824918220986)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 121 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5A3Square.coeff x * exceptional5.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_172 :
    recurrence5ExceptionalProduct.coeff 172 =
      (
        (((65808060524211987551615109281848226305117130223416970161 * 10 ^ 70 +
          3148372953984118496872489855845525600133869539712863826348448900394651) * 10 ^ 70 +
          1094052620195265718891481597077037092631057351437286862347966880978781)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 122 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5A3Square.coeff x * exceptional5.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_173 :
    recurrence5ExceptionalProduct.coeff 173 =
      (
        -(((86363853837619794731915528394531319203005152424113120054 * 10 ^ 70 +
          6912194550332070183592907182306930704864968520968069099479663540561191) * 10 ^ 70 +
          4156022628600593228675986512244790722559828591326802645910907191640133)) /
        (2730860674060914803335210 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 123 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5A3Square.coeff x * exceptional5.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_174 :
    recurrence5ExceptionalProduct.coeff 174 =
      (
        (((1103355831416844124742610914949931851491677648313367330106 * 10 ^ 70 +
          6354161326213061715261308245346437249958262813854223340055267898555851) * 10 ^ 70 +
          3291987024348595938789346664524575102392874848620853078834811684130191)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 124 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5A3Square.coeff x * exceptional5.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_175 :
    recurrence5ExceptionalProduct.coeff 175 =
      (
        -(((1371438345241220324024992749611403721730980142714055388592 * 10 ^ 70 +
          3706816958764843625513008084685754286053355621861176987036460506173540) * 10 ^ 70 +
          8474773833730530570658853377667790755964796784068286487782231723100443)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 125 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5A3Square.coeff x * exceptional5.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_176 :
    recurrence5ExceptionalProduct.coeff 176 =
      (
        (((828638485308582983235121437431536479603052756204480959416 * 10 ^ 70 +
          0352047508018954799901421893251403802711200100843414827438663022107082) * 10 ^ 70 +
          8558274038482928575180451907697782308302032529169398891184173265066629)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 126 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5A3Square.coeff x * exceptional5.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_177 :
    recurrence5ExceptionalProduct.coeff 177 =
      (
        -(((1945215798171370786464324163657833102787814564705650558401 * 10 ^ 70 +
          6463497225329630560829037895876832862861399649243878975772204021983706) * 10 ^ 70 +
          4560439004073791180890331711254338124621639770066397676376464598019657)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 127 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5A3Square.coeff x * exceptional5.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_178 :
    recurrence5ExceptionalProduct.coeff 178 =
      (
        (((443002590431115668398707689841739076855829403289814010585 * 10 ^ 70 +
          0528759041013192065964354275660567964189957780929457397868845436074218) * 10 ^ 70 +
          9292853463455867974045137776169834054169829054956315793738938848966961)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 128 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5A3Square.coeff x * exceptional5.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_179 :
    recurrence5ExceptionalProduct.coeff 179 =
      (
        -(((1221562967672802961089957298333343708165130611542022618209 * 10 ^ 70 +
          5837985738665287338485504192554824297216042917033519650425618019590301) * 10 ^ 70 +
          8762130811768545462669858009520584403864628376145559782750938461128621)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 129 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5A3Square.coeff x * exceptional5.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_180 :
    recurrence5ExceptionalProduct.coeff 180 =
      (
        (((651207205728594260480570320535550700690782226578979486023 * 10 ^ 70 +
          8016577757701386190820253392762998563995022863988043719049884233679798) * 10 ^ 70 +
          5049826568197174914172736797563160700019527782163623102994629643856966)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 130 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence5A3Square.coeff x * exceptional5.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_181 :
    recurrence5ExceptionalProduct.coeff 181 =
      (
        -(((669251808165016205327247363065153920736835213375274524789 * 10 ^ 70 +
          8073235569276777733861894083622825935364038960205904031939308177363045) * 10 ^ 70 +
          2420545700008655367761028030490304687806909451558232978189391753524748)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 131 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence5A3Square.coeff x * exceptional5.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_182 :
    recurrence5ExceptionalProduct.coeff 182 =
      (
        (((528261533663734782633860999341333974659999155638381523538 * 10 ^ 70 +
          5170819237029227152054777054212571763081925504400393584613786016488533) * 10 ^ 70 +
          2194635478964658452035684409335582659509061450764804552054403806617671)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 132 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence5A3Square.coeff x * exceptional5.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_183 :
    recurrence5ExceptionalProduct.coeff 183 =
      (
        -(((2487179144664415611742669124747685104173729820099333626129 * 10 ^ 70 +
          2252810607839689286025731925025230967162594617568964511088694534261504) * 10 ^ 70 +
          0444572697051892550208617634430079342355798793485460668807132972605861)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 133 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence5A3Square.coeff x * exceptional5.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_184 :
    recurrence5ExceptionalProduct.coeff 184 =
      (
        (((2214276576701147336802474906325754461461971638289451016394 * 10 ^ 70 +
          5585913134055381300447168964238942065879309953865553084821575050160782) * 10 ^ 70 +
          2433884989393620914093999554526180283984260775644749085324279948818401)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 134 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence5A3Square.coeff x * exceptional5.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_185 :
    recurrence5ExceptionalProduct.coeff 185 =
      (
        -(((916863540417391722879918751811456488849053750227917024268 * 10 ^ 70 +
          0520243116029827609131381333172965513442721854897020527526128694467559) * 10 ^ 70 +
          2532738767783782106938292849529525880581923631983127575053196211893059)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 135 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence5A3Square.coeff x * exceptional5.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_186 :
    recurrence5ExceptionalProduct.coeff 186 =
      (
        (((683950969215806748418808178790105242544553548055927159363 * 10 ^ 70 +
          3639784736659159194289388431064675986933975523573184021360724484866959) * 10 ^ 70 +
          3649910756205729903732855942479894269641421510645697330116545748603491)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 136 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence5A3Square.coeff x * exceptional5.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_187 :
    recurrence5ExceptionalProduct.coeff 187 =
      (
        -(((424286096974893387615709684638877864314873121653578603807 * 10 ^ 70 +
          5155880973545304995314378277716101877906778809672919746242714403473727) * 10 ^ 70 +
          5403564051527112202637670230720703097363199817664504622858366616910451)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 137 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence5A3Square.coeff x * exceptional5.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_188 :
    recurrence5ExceptionalProduct.coeff 188 =
      (
        (((12544508487834933400907522683583430027988390550752681463 * 10 ^ 70 +
          2924749271379776924163513194322285223421628010787181945275036753099547) * 10 ^ 70 +
          6779705604719281409887257033025227930252598370300711721577696016428527)) /
        (1092344269624365921334084 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 138 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence5A3Square.coeff x * exceptional5.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_189 :
    recurrence5ExceptionalProduct.coeff 189 =
      (
        (((197301636642598366452060541627438512638104171507439095492 * 10 ^ 70 +
          0127501301820653256257309105678513767204822242598366418095378435258116) * 10 ^ 70 +
          5602259231092925416859896822803090416099074962067507580014529766617751)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 139 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence5A3Square.coeff x * exceptional5.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_190 :
    recurrence5ExceptionalProduct.coeff 190 =
      (
        -(((4374029744452872475865386704037260510387444672680260656 * 10 ^ 70 +
          5842828160546004297591603542754554023963243913675994458234974924153199) * 10 ^ 70 +
          4229535555505574395473146108686690173887604568617608903438482351191921)) /
        (184517613112223973198325 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 140 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence5A3Square.coeff x * exceptional5.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_191 :
    recurrence5ExceptionalProduct.coeff 191 =
      (
        (((1006877411572929582254531550321539548469443238815478176090 * 10 ^ 70 +
          0859630988459197028039777522672647573758352260475341343511410678437778) * 10 ^ 70 +
          9419579973932852010500184714309745433559216260105128290319373054922527)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 141 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence5A3Square.coeff x * exceptional5.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_192 :
    recurrence5ExceptionalProduct.coeff 192 =
      (
        -(((314138060283410746178108028676687659872419826587144831886 * 10 ^ 70 +
          1217657696357426356217934503345142913951762031960781327667022660080758) * 10 ^ 70 +
          2004406158315837955460344247418354299690593203930027932632783851889629)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 142 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence5A3Square.coeff x * exceptional5.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_193 :
    recurrence5ExceptionalProduct.coeff 193 =
      (
        (((1389109641408994380267292878955575699243593714259234330688 * 10 ^ 70 +
          9767767804055476755130414622201662827994982660939564192458665960868715) * 10 ^ 70 +
          9705348319231037038264974689278692232984950689339210077501512951460363)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 143 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence5A3Square.coeff x * exceptional5.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_194 :
    recurrence5ExceptionalProduct.coeff 194 =
      (
        -(((352314912723856538046496057057963255891085998633299383448 * 10 ^ 70 +
          2574295906640118844349483789015432543938466210710074379454835796767263) * 10 ^ 70 +
          4794855422879194036522647585516351687279081838511485855636651871643958)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 144 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence5A3Square.coeff x * exceptional5.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_195 :
    recurrence5ExceptionalProduct.coeff 195 =
      (
        (((1332011959701253856120909787744141744190322509676221586801 * 10 ^ 70 +
          1863106261209456619746331343222381455286263430728916402356832507693479) * 10 ^ 70 +
          3172595603775803240214514300242401777059242594024027351274656833194269)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 145 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence5A3Square.coeff x * exceptional5.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_196 :
    recurrence5ExceptionalProduct.coeff 196 =
      (
        -(((294941212171164783351540503702674942053384825290463566398 * 10 ^ 70 +
          8172520745952389855161809842669732172310657943559495071870506024199042) * 10 ^ 70 +
          5382253714154790346605350804585892515776231270841121891344354109791439)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 146 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence5A3Square.coeff x * exceptional5.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_197 :
    recurrence5ExceptionalProduct.coeff 197 =
      (
        (((978735930169395159834751928266862236771698522536953472339 * 10 ^ 70 +
          4899330785092837244333672116906080537695627192834630621394331234929028) * 10 ^ 70 +
          5464754744799691927279966230152364689157536144474214463106211442328729)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 147 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence5A3Square.coeff x * exceptional5.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_198 :
    recurrence5ExceptionalProduct.coeff 198 =
      (
        -(((188839752835450207643961579913655377279618970153533426669 * 10 ^ 70 +
          2005874554173731559645633475499807673342488981662596968396362715031088) * 10 ^ 70 +
          5409939165848410477384378720922637737211025251638245799291553472005157)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 148 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence5A3Square.coeff x * exceptional5.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_199 :
    recurrence5ExceptionalProduct.coeff 199 =
      (
        (((106640007935848387859526792803514552818133277505449914953 * 10 ^ 70 +
          9097750536455730268454781913075797988466191321404145415899063069542128) * 10 ^ 70 +
          8607571643561780489766845550613420495576108803045796809044351243767673)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 149 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence5A3Square.coeff x * exceptional5.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_200 :
    recurrence5ExceptionalProduct.coeff 200 =
      (
        -(((165389314995804490270744810209392437888966292175427914427 * 10 ^ 70 +
          9721969581295321166945579199838550370226641763590108474515130142079379) * 10 ^ 70 +
          3529348488476148827114437081824787039088949810750610176344721512897643)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 150 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence5A3Square.coeff x * exceptional5.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_201 :
    recurrence5ExceptionalProduct.coeff 201 =
      (
        (((32093440296294080387453470996170135917109519825858727763 * 10 ^ 70 +
          2497049294282258551589897991832705799720519572007057976555278011819260) * 10 ^ 70 +
          2641483014428493453556650245920088836758130618037450148344533893956793)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 151 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence5A3Square.coeff x * exceptional5.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_202 :
    recurrence5ExceptionalProduct.coeff 202 =
      (
        -(((7107105732437074804307072951582324083416016657198051393 * 10 ^ 70 +
          5945822564512927759720359293427205517833907745707109148706199700651194) * 10 ^ 70 +
          7222869598263770585231528412677288242656505001894448762530287757711088)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 152 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence5A3Square.coeff x * exceptional5.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_203 :
    recurrence5ExceptionalProduct.coeff 203 =
      (
        -(((64614152578022965381822761971222665974277444415571169218 * 10 ^ 70 +
          9351085342118233218195372256713401913937348167727047806513394072573979) * 10 ^ 70 +
          1985372292258607857409949777959635688720477349326584563560241469671477)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 153 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence5A3Square.coeff x * exceptional5.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_204 :
    recurrence5ExceptionalProduct.coeff 204 =
      (
        (((61036359811801735833932818398556882083641078147441089066 * 10 ^ 70 +
          3259063203373194620569825815016722739083058893297276799049619836990334) * 10 ^ 70 +
          6732848526981150274578907698750735314747436122325485062871385825927599)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 154 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5A3Square.coeff x * exceptional5.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_205 :
    recurrence5ExceptionalProduct.coeff 205 =
      (
        -(((5999184678583558489745402789712247427225573008141357044 * 10 ^ 70 +
          6309128267709248839419160173096222734915811986187898244692388533410639) * 10 ^ 70 +
          3172767198466575935017161071140888509872991402609955026935617090670487)) /
        (1092344269624365921334084 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 155 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5A3Square.coeff x * exceptional5.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_206 :
    recurrence5ExceptionalProduct.coeff 206 =
      (
        (((77768609187864365056909926365518623453124299692423242508 * 10 ^ 70 +
          6918914250081443007298244645206525079180526699666881140985545887400525) * 10 ^ 70 +
          1790656499761870169284942855724785697764915142529251415233256904074761)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 156 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5A3Square.coeff x * exceptional5.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_207 :
    recurrence5ExceptionalProduct.coeff 207 =
      (
        -(((145928667040997265593647979055774383961762168667709801504 * 10 ^ 70 +
          2565807343539096135822997262541196502242340804568676340050709009731938) * 10 ^ 70 +
          3880979238964481798594881796919090503849117400874635217191014833547573)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 157 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5A3Square.coeff x * exceptional5.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_208 :
    recurrence5ExceptionalProduct.coeff 208 =
      (
        (((63744454961156101618997382866366671275022237167234475753 * 10 ^ 70 +
          8194008547233149987367657898139429206726003389790815353393421656079585) * 10 ^ 70 +
          4282728141109854800489971719892710307697652494365469811977746238293231)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 158 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5A3Square.coeff x * exceptional5.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_209 :
    recurrence5ExceptionalProduct.coeff 209 =
      (
        -(((2844551217047169228062096504368828618905588949464472094 * 10 ^ 70 +
          3982769411649052373870180496429162545129096349083553794511841553779576) * 10 ^ 70 +
          7629428166312386711238809056713733599942229588911555510800007890186449)) /
        (738070452448895892793300 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 159 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5A3Square.coeff x * exceptional5.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_210 :
    recurrence5ExceptionalProduct.coeff 210 =
      (
        (((41398964653295608844094650420697524363965139747955737250 * 10 ^ 70 +
          9663198511029406992623727178667339659886042013413185434991837409071285) * 10 ^ 70 +
          0984254130971308898965489078950227833397184399714633110032721811239071)) /
        (13654303370304574016676050 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 160 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5A3Square.coeff x * exceptional5.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_211 :
    recurrence5ExceptionalProduct.coeff 211 =
      (
        -(((62388009182437979225359372710959813529240276402824406644 * 10 ^ 70 +
          6562816422491793255783444839172018435396474075185400527084706084436761) * 10 ^ 70 +
          5545496820281874327373606857657653724551032067727549854517137519856443)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 161 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5A3Square.coeff x * exceptional5.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_212 :
    recurrence5ExceptionalProduct.coeff 212 =
      (
        (((11291819889088520304926013963041297316061500035955696859 * 10 ^ 70 +
          4621023304462993028386680273596003627557217125166339658972146255068982) * 10 ^ 70 +
          1329063142426577457429798190925311120480029715231412865838472482698058)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 162 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5A3Square.coeff x * exceptional5.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_213 :
    recurrence5ExceptionalProduct.coeff 213 =
      (
        -(((31475689477903277185047671605095951840568482305085407332 * 10 ^ 70 +
          3435073824786003063365134055900121639798564056732323167313042164195723) * 10 ^ 70 +
          7568718400337067265758282010736812831776511597267793789707634835668751)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 163 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5A3Square.coeff x * exceptional5.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_214 :
    recurrence5ExceptionalProduct.coeff 214 =
      (
        (((21129697979458854234216058213218062337239788240186420732 * 10 ^ 70 +
          0185557606096761426769099316109085021364531674841234540118431046461528) * 10 ^ 70 +
          7652132539580782660363228604020573706896550810618666524053349334900971)) /
        (27308606740609148033352100 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 164 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5A3Square.coeff x * exceptional5.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_215 :
    recurrence5ExceptionalProduct.coeff 215 =
      (
        -(((3415400207133351596665287948288100077742193614386964947 * 10 ^ 70 +
          3878972704720941573073551157712403519841095718958159359594927786388995) * 10 ^ 70 +
          3488943248055889863565938622966744676080951581788141059354874086204099)) /
        (6827151685152287008338025 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 165 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5ExceptionalProduct_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5A3Square.coeff x * exceptional5.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5Exceptional_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5ExceptionalProduct_coeff_216 :
    recurrence5ExceptionalProduct.coeff 216 =
      (
        (((1699397976093900413393487945077241043013702642031945175 * 10 ^ 70 +
          6722502256974818605494011830398896170054455077767423602568446619537424) * 10 ^ 70 +
          5784557996733020767866555827537766038584203607122163472854891246060329)) /
        (5461721348121829606670420 : ℚ)
      ) := by
  unfold recurrence5ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 166 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5ExceptionalProduct_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
