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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
