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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
