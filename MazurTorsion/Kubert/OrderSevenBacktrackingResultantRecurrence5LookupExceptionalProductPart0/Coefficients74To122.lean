/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3Square
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptional
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalProductPart0Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
