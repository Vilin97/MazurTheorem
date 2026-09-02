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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
