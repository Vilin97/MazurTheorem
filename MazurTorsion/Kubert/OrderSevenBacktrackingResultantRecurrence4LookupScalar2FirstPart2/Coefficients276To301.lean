/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59

attribute [local simp]
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123

attribute [local simp]
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_170
  recurrence4B3A4_coeff_171
  recurrence4B3A4_coeff_172
  recurrence4B3A4_coeff_173
  recurrence4B3A4_coeff_174
  recurrence4B3A4_coeff_175
  recurrence4B3A4_coeff_176
  recurrence4B3A4_coeff_177
  recurrence4B3A4_coeff_178
  recurrence4B3A4_coeff_179
  recurrence4B3A4_coeff_180
  recurrence4B3A4_coeff_181
  recurrence4B3A4_coeff_182
  recurrence4B3A4_coeff_183
  recurrence4B3A4_coeff_184
  recurrence4B3A4_coeff_185
  recurrence4B3A4_coeff_186
  recurrence4B3A4_coeff_187

attribute [local simp]
  recurrence4B3A4_coeff_188
  recurrence4B3A4_coeff_189
  recurrence4B3A4_coeff_190
  recurrence4B3A4_coeff_191
  recurrence4B3A4_coeff_192
  recurrence4B3A4_coeff_193
  recurrence4B3A4_coeff_194
  recurrence4B3A4_coeff_195
  recurrence4B3A4_coeff_196
  recurrence4B3A4_coeff_197
  recurrence4B3A4_coeff_198
  recurrence4B3A4_coeff_199
  recurrence4B3A4_coeff_200
  recurrence4B3A4_coeff_201
  recurrence4B3A4_coeff_202
  recurrence4B3A4_coeff_203
  recurrence4B3A4_coeff_204
  recurrence4B3A4_coeff_205
  recurrence4B3A4_coeff_206
  recurrence4B3A4_coeff_207
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_210
  recurrence4B3A4_coeff_211
  recurrence4B3A4_coeff_212
  recurrence4B3A4_coeff_213
  recurrence4B3A4_coeff_214
  recurrence4B3A4_coeff_215
  recurrence4B3A4_coeff_216
  recurrence4B3A4_coeff_217
  recurrence4B3A4_coeff_218
  recurrence4B3A4_coeff_219
  recurrence4B3A4_coeff_220
  recurrence4B3A4_coeff_221
  recurrence4B3A4_coeff_222
  recurrence4B3A4_coeff_223
  recurrence4B3A4_coeff_224
  recurrence4B3A4_coeff_225
  recurrence4B3A4_coeff_226
  recurrence4B3A4_coeff_227
  recurrence4B3A4_coeff_228
  recurrence4B3A4_coeff_229
  recurrence4B3A4_coeff_230
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_240
  recurrence4B3A4_coeff_241
  recurrence4B3A4_coeff_242
  recurrence4B3A4_coeff_243
  recurrence4B3A4_coeff_244
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251

attribute [local simp]
  recurrence4B3A4_coeff_252
  recurrence4B3A4_coeff_253
  recurrence4B3A4_coeff_254
  recurrence4B3A4_coeff_255
  recurrence4B3A4_coeff_256
  recurrence4B3A4_coeff_257
  recurrence4B3A4_coeff_258
  recurrence4B3A4_coeff_259
  recurrence4B3A4_coeff_260
  recurrence4B3A4_coeff_261
  recurrence4B3A4_coeff_262
  recurrence4B3A4_coeff_263
  recurrence4B3A4_coeff_264
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
  recurrence4B3A4_coeff_275
  recurrence4B3A4_coeff_276
  recurrence4B3A4_coeff_277
  recurrence4B3A4_coeff_278
  recurrence4B3A4_coeff_279
  recurrence4B3A4_coeff_280
  recurrence4B3A4_coeff_281
  recurrence4B3A4_coeff_282
  recurrence4B3A4_coeff_283
  recurrence4B3A4_coeff_284
  recurrence4B3A4_coeff_285
  recurrence4B3A4_coeff_286
  recurrence4B3A4_coeff_287
  recurrence4B3A4_coeff_288
  recurrence4B3A4_coeff_289
  recurrence4B3A4_coeff_290
  recurrence4B3A4_coeff_291
  recurrence4B3A4_coeff_292
  recurrence4B3A4_coeff_293
  recurrence4B3A4_coeff_294
  recurrence4B3A4_coeff_295
  recurrence4B3A4_coeff_296
  recurrence4B3A4_coeff_297
  recurrence4B3A4_coeff_298
  recurrence4B3A4_coeff_299
  recurrence4B3A4_coeff_300
  recurrence4B3A4_coeff_301
  recurrence4B3A4_coeff_302
  recurrence4B3A4_coeff_303
  recurrence4B3A4_coeff_304
  recurrence4B3A4_coeff_305
  recurrence4B3A4_coeff_306
  recurrence4B3A4_coeff_307
  recurrence4B3A4_coeff_308
  recurrence4B3A4_coeff_309
  recurrence4B3A4_coeff_310
  recurrence4B3A4_coeff_311
  recurrence4B3A4_coeff_312
  recurrence4B3A4_coeff_313
  recurrence4B3A4_coeff_314
  recurrence4B3A4_coeff_315

attribute [local simp]
  recurrence4B3A4_coeff_316
  recurrence4B3A4_coeff_317
  recurrence4B3A4_coeff_318
  recurrence4B3A4_coeff_319
  recurrence4B3A4_coeff_320
  recurrence4B3A4_coeff_321
  recurrence4B3A4_coeff_322
  recurrence4B3A4_coeff_323
  recurrence4B3A4_coeff_324
  recurrence4B3A4_coeff_325
  recurrence4B3A4_coeff_326
  recurrence4B3A4_coeff_327
  recurrence4B3A4_coeff_328
  recurrence4B3A4_coeff_329
  recurrence4B3A4_coeff_330
  recurrence4B3A4_coeff_331
  recurrence4B3A4_coeff_332
  recurrence4B3A4_coeff_333
  recurrence4B3A4_coeff_334
  recurrence4B3A4_coeff_335
  recurrence4B3A4_coeff_336
  recurrence4B3A4_coeff_337
  recurrence4B3A4_coeff_338
  recurrence4B3A4_coeff_339
  recurrence4B3A4_coeff_340
  recurrence4B3A4_coeff_341
  recurrence4B3A4_coeff_342

private theorem recurrence4Scalar2First_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (276 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (276 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_276 :
    recurrence4Scalar2First.coeff 276 =
      -(((((48522100818657967708381789 * 10 ^ 70 +
        7199466601201320980801610439206677798309504220965417149324599021697196) * 10 ^ 70 +
        6636585573113732760298662677643326735577214236798387089192146085035705) * 10 ^ 70 +
        5092994813730320350836943949248013916996793645062752451154944179383241) * 10 ^ 70 +
        6444920730609506540300333653615440053509389796705474585901679475284903) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (276 - x)) = _
  rw [show 277 = 1 +
    276 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 12 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (277 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (277 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_277 :
    recurrence4Scalar2First.coeff 277 =
      (((((31248238688200886238344287 * 10 ^ 70 +
        6857032188861160335105202309352578713939954577688963494706266158789379) * 10 ^ 70 +
        8253593411117794107280546890383093958073349272256885383312405179373319) * 10 ^ 70 +
        7349606882477431337177942045558896161416662775854933657833053788981737) * 10 ^ 70 +
        4420324342012826666324595388518640737039761605952040139844953503026134) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (277 - x)) = _
  rw [show 278 = 1 +
    277 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 277 = 32 +
      245 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 12 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (278 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (278 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_278 :
    recurrence4Scalar2First.coeff 278 =
      -(((((18577214593598705575552717 * 10 ^ 70 +
        0572100459113791631255025082408850676890280205432736874628035182574002) * 10 ^ 70 +
        1232316907794253734402432663163650506682580111372027138294060186533964) * 10 ^ 70 +
        0506039281142120086609989709796039148667007230709867927455451529098223) * 10 ^ 70 +
        2142518992067900558536012822075690168062691940439676315107604761101749) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (278 - x)) = _
  rw [show 279 = 1 +
    278 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 278 = 32 +
      246 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 12 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (279 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (279 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_279 :
    recurrence4Scalar2First.coeff 279 =
      (((((9695942635763157059775102 * 10 ^ 70 +
        7614806285057573119595471968810769715376936139305496294431449760211560) * 10 ^ 70 +
        0824148193450824662455242316369281126300067405957921742166527735117326) * 10 ^ 70 +
        5895342455673744047985921854784647562353205147543704587121570029514120) * 10 ^ 70 +
        6068187956693468470674285079130662493420934616931190288138103881095258) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (279 - x)) = _
  rw [show 280 = 1 +
    279 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 12 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (280 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (280 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_280 :
    recurrence4Scalar2First.coeff 280 =
      -(((((3799399646711910592678873 * 10 ^ 70 +
        1444603377032064125993530049648144148797034879594152079008147660949122) * 10 ^ 70 +
        7456307163596987807105814669361212801899020217964092438706392874393096) * 10 ^ 70 +
        7191875482637930714433334894526601523211198301558115769811482055740891) * 10 ^ 70 +
        3388714292665339651948167965285030052956445426397511075093092175493239) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (280 - x)) = _
  rw [show 281 = 1 +
    280 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 280 = 32 +
      248 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 12 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (281 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (281 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_281 :
    recurrence4Scalar2First.coeff 281 =
      (((((151119169860574436202482 * 10 ^ 70 +
        8686206246679467700149004204296841010057469892742347942605433668722309) * 10 ^ 70 +
        2160417967403371498703417491518117444689856568695590363550217878189610) * 10 ^ 70 +
        7417673189873704673125399527069706804389329445346202935148467110655839) * 10 ^ 70 +
        6150779749694779239306745311863691403926334093368074803337452077063053) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (281 - x)) = _
  rw [show 282 = 1 +
    281 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 281 = 32 +
      249 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 12 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (282 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (282 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_282 :
    recurrence4Scalar2First.coeff 282 =
      (((((1881884979640884940108391 * 10 ^ 70 +
        7633661867322862376986910499470463571261845570331084774039740010769963) * 10 ^ 70 +
        0667072252205975815953685253026924235484093208829982757670851280121416) * 10 ^ 70 +
        8986300435507388468740948511085606561328014590392888278167534013176077) * 10 ^ 70 +
        8586026061503356108652104445158304005251685210219202088503167558253870) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (282 - x)) = _
  rw [show 283 = 1 +
    282 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 12 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (283 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (283 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_283 :
    recurrence4Scalar2First.coeff 283 =
      -(((((2814924447669287645049976 * 10 ^ 70 +
        5431343417333641913758940651320039280757494267683450688409934439621103) * 10 ^ 70 +
        5781901946801868729806840836437071925137589618980713873944807842952432) * 10 ^ 70 +
        6993297326216682843891844017393298306872226856991574119786239058629690) * 10 ^ 70 +
        8601542216849282463970233948002770837523293418338798515253773049895175) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (283 - x)) = _
  rw [show 284 = 1 +
    283 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 283 = 32 +
      251 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 12 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (284 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (284 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_284 :
    recurrence4Scalar2First.coeff 284 =
      (((((3046693384612451828715750 * 10 ^ 70 +
        3596013844700029459746284277297361354973783472493080516829773868671721) * 10 ^ 70 +
        1811254962311969189505284160441516894144734978852006369366387537372925) * 10 ^ 70 +
        7121526488846915051067246783965573030777039768068197543080973394860716) * 10 ^ 70 +
        5784190919041110235258002888486055872096565332104531675916531951804089) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (284 - x)) = _
  rw [show 285 = 1 +
    284 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 284 = 32 +
      252 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 252 = 32 +
      220 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 12 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (285 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (285 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_285 :
    recurrence4Scalar2First.coeff 285 =
      -(((((2870287302854323860542813 * 10 ^ 70 +
        1119549478987837610054091668733995025078312139907254153493529192791360) * 10 ^ 70 +
        4236258563643779217112324506169406116246538141991427452817586168496175) * 10 ^ 70 +
        9304309686891106013115914616465783504863118650524582356436999421483499) * 10 ^ 70 +
        4605568451726895775842120058772695258174767891728883932683274137575493) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (285 - x)) = _
  rw [show 286 = 1 +
    285 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 285 = 32 +
      253 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 253 = 32 +
      221 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 12 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (286 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (286 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_286 :
    recurrence4Scalar2First.coeff 286 =
      (((((2489626158958416473678036 * 10 ^ 70 +
        2131820968479511992384261869682005518965968981721596540110195084669437) * 10 ^ 70 +
        7897068486007537503686742135415720322691820906771118386855117253937512) * 10 ^ 70 +
        5627376945801129320097217996272885607088544868813297586573923461551731) * 10 ^ 70 +
        6691062477006160215491354302117311059755883283575987737804429571009295) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (286 - x)) = _
  rw [show 287 = 1 +
    286 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 286 = 32 +
      254 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 254 = 32 +
      222 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 12 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (287 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (287 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_287 :
    recurrence4Scalar2First.coeff 287 =
      -(((((2037732991462505299883976 * 10 ^ 70 +
        2530808631547530312394688263453826439256488686472877981319569585063147) * 10 ^ 70 +
        7358739063275511832258010920109846373334451626069154415494462082442160) * 10 ^ 70 +
        0801724314803125553933085989836766456906484805608678029024267618077568) * 10 ^ 70 +
        7659953596206791292000022984503885692588184802286594437029249843496255) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (287 - x)) = _
  rw [show 288 = 1 +
    287 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 287 = 32 +
      255 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 255 = 32 +
      223 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 12 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (288 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (288 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_288 :
    recurrence4Scalar2First.coeff 288 =
      (((((1594388006484397285608947 * 10 ^ 70 +
        4271288664430468626163216075870835663889481774463123795528538953826475) * 10 ^ 70 +
        9154401423226326742997733455469379780705102140151435776016583410841044) * 10 ^ 70 +
        3791883930895318963709382870635947681057946574804487000414596523624637) * 10 ^ 70 +
        0967581115688219487248272264692086103802858364066822586841625650750288) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (288 - x)) = _
  rw [show 289 = 1 +
    288 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 288 = 32 +
      256 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 256 = 32 +
      224 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 12 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (289 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (289 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_289 :
    recurrence4Scalar2First.coeff 289 =
      -(((((1201653239076549339583510 * 10 ^ 70 +
        3021229949382253202893135518950729455024934244138354910876487851962707) * 10 ^ 70 +
        8187223070019686313139355849249467057655107140264715865074925770983890) * 10 ^ 70 +
        4409107996000017829773362803952139671226630199522902672282490979720592) * 10 ^ 70 +
        7931773254124918545325900446937353125896512968741639380332518322697604) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (289 - x)) = _
  rw [show 290 = 1 +
    289 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 289 = 32 +
      257 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 257 = 32 +
      225 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 12 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (290 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (290 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_290 :
    recurrence4Scalar2First.coeff 290 =
      (((((876556731205812987243675 * 10 ^ 70 +
        9739378435223166934435832807690199686642888841330372509873139188509835) * 10 ^ 70 +
        0975043344121545310205821998688476407362274218245454662829955777823314) * 10 ^ 70 +
        5427914732529432208594200531690221707173866582116220744727754584474494) * 10 ^ 70 +
        0818215127967267294843359476432859550534208161966382756992611770218458) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (290 - x)) = _
  rw [show 291 = 1 +
    290 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 290 = 32 +
      258 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 258 = 32 +
      226 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 12 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (291 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (291 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_291 :
    recurrence4Scalar2First.coeff 291 =
      -(((((620804693388669633088473 * 10 ^ 70 +
        5720550412085266588162181954301033647392083626771678631512712508160157) * 10 ^ 70 +
        8765685099961138782553451827303327618737249234314164348538969287064265) * 10 ^ 70 +
        2710093396061922946899661608229797248623857221660539142292593012406808) * 10 ^ 70 +
        5046287589541362440908527235033580770562822573045478127353355613897105) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (291 - x)) = _
  rw [show 292 = 1 +
    291 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 291 = 32 +
      259 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 259 = 32 +
      227 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 12 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (292 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (292 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_292 :
    recurrence4Scalar2First.coeff 292 =
      (((((427762959870156864954229 * 10 ^ 70 +
        1251126211889510204544248702102428032443238836904078196755383113386145) * 10 ^ 70 +
        5714637861797168990252193062937612932235939728684342066629161908353913) * 10 ^ 70 +
        4335085521521578416022375471837181811355912752034398835219739763607140) * 10 ^ 70 +
        3078162223841354012689321696961505632555352693571205315228506969845648) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (292 - x)) = _
  rw [show 293 = 1 +
    292 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 292 = 32 +
      260 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 260 = 32 +
      228 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 12 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (293 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (293 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_293 :
    recurrence4Scalar2First.coeff 293 =
      -(((((287147555998307721527024 * 10 ^ 70 +
        5213862048458877604486857730298392360170120945157492395273667707797845) * 10 ^ 70 +
        0174730016096839794025187515365186514718280274396633876298735759234828) * 10 ^ 70 +
        4482129034445869798886277380386563516350725665893241591236883811818711) * 10 ^ 70 +
        4903770707938735413558918688083033426871140778284378513221666719690368) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (293 - x)) = _
  rw [show 294 = 1 +
    293 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 293 = 32 +
      261 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 261 = 32 +
      229 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 12 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (294 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (294 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_294 :
    recurrence4Scalar2First.coeff 294 =
      (((((187931675983636845703449 * 10 ^ 70 +
        1817390398047223493353598494537947035972800677651235602047414513406191) * 10 ^ 70 +
        1526666337662013790661025156014716405803011586076531511274701937560671) * 10 ^ 70 +
        4967953401066980269266021753367474196462924473003120730955059291485502) * 10 ^ 70 +
        9629352341000659322920607000389737390061318055425073387786193635341251) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (294 - x)) = _
  rw [show 295 = 1 +
    294 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 294 = 32 +
      262 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 262 = 32 +
      230 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (295 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (295 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_295 :
    recurrence4Scalar2First.coeff 295 =
      -(((((119956748524812240008004 * 10 ^ 70 +
        8897041122966674429199132200940853629583897980929436415284788406759532) * 10 ^ 70 +
        9891446330178493003826683065814555147329293559071282616511547058367357) * 10 ^ 70 +
        6866880472063537984677701927773730970103207113572578236975874557136792) * 10 ^ 70 +
        9893058317732079888010773762666525220345939113181264016543530265939027) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (295 - x)) = _
  rw [show 296 = 1 +
    295 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 295 = 32 +
      263 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 263 = 32 +
      231 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 12 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (296 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (296 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_296 :
    recurrence4Scalar2First.coeff 296 =
      (((((74666604179186311349774 * 10 ^ 70 +
        9808000955286888353211653234870054766790651106582908056200445209537224) * 10 ^ 70 +
        5784972181979546606532106091320318675869319913072326127161208261868074) * 10 ^ 70 +
        1313716251914829621793542612476980537689212947080275285841971672792427) * 10 ^ 70 +
        6658339031240008256776077807328550906509787591164018223884268434840741) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (296 - x)) = _
  rw [show 297 = 1 +
    296 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 296 = 32 +
      264 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 264 = 32 +
      232 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 12 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (297 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (297 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_297 :
    recurrence4Scalar2First.coeff 297 =
      -(((((45295159533981772610208 * 10 ^ 70 +
        7096832790994729202668136520184851412157088326829207573838460462878292) * 10 ^ 70 +
        2711116525240025376299730480070373663321002313158242350963090841036794) * 10 ^ 70 +
        6805726370246521410977255087056587384947578680922222457009087386852987) * 10 ^ 70 +
        7356412792501406873831425424602944154233561082006616869206829872855427) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (297 - x)) = _
  rw [show 298 = 1 +
    297 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 297 = 32 +
      265 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 265 = 32 +
      233 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 12 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (298 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (298 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_298 :
    recurrence4Scalar2First.coeff 298 =
      (((((26749157438209690712570 * 10 ^ 70 +
        3869068800976178296913772111833921614909570431061947864759082773511537) * 10 ^ 70 +
        4701693148494486539484860692000465332364864647321655800341569114968367) * 10 ^ 70 +
        5683925241560113379066671184959639287498584654879911019191262540992227) * 10 ^ 70 +
        5654399622599193537456396961958705151859393683743618412195473925755215) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (298 - x)) = _
  rw [show 299 = 1 +
    298 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 298 = 32 +
      266 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 266 = 32 +
      234 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 12 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (299 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (299 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_299 :
    recurrence4Scalar2First.coeff 299 =
      -(((((15349688967404990330584 * 10 ^ 70 +
        1947381575152355194019069184012630432711442945269225875998513207288786) * 10 ^ 70 +
        9700845520123732368759552682866428875753401036602441956013253781206260) * 10 ^ 70 +
        4453194502745031239993660639445072243366326373014164345290450466040426) * 10 ^ 70 +
        0598761067827361783451999820824300690849638149290235013184235379316767) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (299 - x)) = _
  rw [show 300 = 1 +
    299 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 299 = 32 +
      267 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 267 = 32 +
      235 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 12 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (300 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (300 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_300 :
    recurrence4Scalar2First.coeff 300 =
      (((((8534407223706875522570 * 10 ^ 70 +
        8425896326257204547934493681392839984458996533574076342785452584702790) * 10 ^ 70 +
        0571557711302541868331220192610746253454510039692417429315340956174902) * 10 ^ 70 +
        3497542382043288640871550872751438755332367960542063384088119110333859) * 10 ^ 70 +
        2449649836455352324513013370188675381057978978279180104048341165665235) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (300 - x)) = _
  rw [show 301 = 1 +
    300 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 300 = 32 +
      268 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 268 = 32 +
      236 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 12 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (301 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (301 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_301 :
    recurrence4Scalar2First.coeff 301 =
      -(((((4577126686650531794508 * 10 ^ 70 +
        1831800327512685880537216725812156484935145051631930315670168765954571) * 10 ^ 70 +
        2517801601803232369492745523762900205842143188926052139355428642952571) * 10 ^ 70 +
        5443668666236834375477572680071785285027457768268595134545379617661140) * 10 ^ 70 +
        9294599618135098656729584825822506784505460565966447851045146644755497) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (301 - x)) = _
  rw [show 302 = 1 +
    301 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 301 = 32 +
      269 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 269 = 32 +
      237 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 12 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
