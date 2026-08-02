/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (302 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (302 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_302 :
    recurrence4Scalar2First.coeff 302 =
      (((((2350978343293408902296 * 10 ^ 70 +
        7163060501467373884676347968970682674660052954119809068814467580772260) * 10 ^ 70 +
        4950806937452944378627758335956572872439535482241189462026751273038912) * 10 ^ 70 +
        0894596023779738591297861204567308654038324143865498455605342054129033) * 10 ^ 70 +
        2861332333903759709682256132750388855848419607738096334084413446727645) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (302 - x)) = _
  rw [show 303 = 1 +
    302 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 302 = 32 +
      270 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 12 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (303 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (303 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_303 :
    recurrence4Scalar2First.coeff 303 =
      -(((((1142445933958270856080 * 10 ^ 70 +
        6189117464907327396474437662638815873402024824106559378994512589369965) * 10 ^ 70 +
        6716244149757620813264487749522673122218809068434011599324123940172232) * 10 ^ 70 +
        1225650972587925838756062511928115268527448715847643389234094758940984) * 10 ^ 70 +
        4193012967631853103430248890338698232284665699600919872320575530088266) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (303 - x)) = _
  rw [show 304 = 1 +
    303 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 303 = 32 +
      271 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 12 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (304 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (304 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_304 :
    recurrence4Scalar2First.coeff 304 =
      (((((513257842877035667169 * 10 ^ 70 +
        5116332066180545693473164763988234349189493144626860526216856558124411) * 10 ^ 70 +
        9191505994385226949299197026915149402637291903002707611206527622120133) * 10 ^ 70 +
        9931851593348198742090231656623470215744386433383503362645072258637218) * 10 ^ 70 +
        0155249839025789618370072573761645714007452441936354447344173965417815) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (304 - x)) = _
  rw [show 305 = 1 +
    304 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 304 = 32 +
      272 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 12 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (305 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (305 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_305 :
    recurrence4Scalar2First.coeff 305 =
      -(((((202432317926400756013 * 10 ^ 70 +
        1268296256813452016722577912520966998692052550820021215699134375910898) * 10 ^ 70 +
        0310396166259748148197511680477503439731382590736878045382361997515836) * 10 ^ 70 +
        2471246800982139761041442919583500357936532674109132164158182309476228) * 10 ^ 70 +
        3308876753659305524457653658900141048279376053573101496489600562623912) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (305 - x)) = _
  rw [show 306 = 1 +
    305 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 305 = 32 +
      273 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 12 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (306 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (306 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_306 :
    recurrence4Scalar2First.coeff 306 =
      (((((59545950052908872125 * 10 ^ 70 +
        6188488877064029856414702659063856319890881313232066908408625219022113) * 10 ^ 70 +
        8963275732120557441254501101358403425836710963719054572125089470252908) * 10 ^ 70 +
        3127146222733715329358285154855839176917551379940273215330812012021387) * 10 ^ 70 +
        3661863800822207912798334676162869162364356870506046308354148725453141) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (306 - x)) = _
  rw [show 307 = 1 +
    306 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 306 = 32 +
      274 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 12 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (307 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (307 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_307 :
    recurrence4Scalar2First.coeff 307 =
      -(((((918872566419590201 * 10 ^ 70 +
        6257421017316979899330844670887879514005137994218459007664998587151429) * 10 ^ 70 +
        4400435268018476296104487361836897491769113821091940435812546776764251) * 10 ^ 70 +
        5545524385932345067341733535721696051010697309014796510670596941075357) * 10 ^ 70 +
        3282987188148124616950899586831788131336940176365903754636404488860275) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (307 - x)) = _
  rw [show 308 = 1 +
    307 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 307 = 32 +
      275 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (308 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (308 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_308 :
    recurrence4Scalar2First.coeff 308 =
      -(((((18163917094428496012 * 10 ^ 70 +
        5554579324897153825661062214191793880506950778505202422884864661434277) * 10 ^ 70 +
        4563475499125782668286855104030010920123046027343403224664242304658665) * 10 ^ 70 +
        1230408942281665546379347043145332587866001738432048507300400368243444) * 10 ^ 70 +
        0970288347573825805510433011041466253752996505579393980351535070784930) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (308 - x)) = _
  rw [show 309 = 1 +
    308 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 308 = 32 +
      276 by norm_num, Finset.sum_range_add]
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
    rw [show 148 = 12 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (309 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (309 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_309 :
    recurrence4Scalar2First.coeff 309 =
      (((((20470094292645426314 * 10 ^ 70 +
        3901815900904452186138061772462989759080370668412352188427135074507216) * 10 ^ 70 +
        0062677902969095992032604638251047752658735402835473258502991450968853) * 10 ^ 70 +
        6966439460178583492080155625035918138293293511298620892731800682421144) * 10 ^ 70 +
        2108272522069941916941849345707861459931277801307709583828652800043671) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (309 - x)) = _
  rw [show 310 = 1 +
    309 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 309 = 32 +
      277 by norm_num, Finset.sum_range_add]
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
    rw [show 149 = 12 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (310 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (310 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_310 :
    recurrence4Scalar2First.coeff 310 =
      -(((((16888889723697081027 * 10 ^ 70 +
        5519423857492563217287579025222216544259353855963105621497452388587543) * 10 ^ 70 +
        3452877782694317978455362163226640552867134059011293141195095318765364) * 10 ^ 70 +
        2228849650489787615071859479449964984591221840223288144349374254224902) * 10 ^ 70 +
        3472380008907804625612666990501585808180378895033817700095681236792687) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (310 - x)) = _
  rw [show 311 = 1 +
    310 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
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
    rw [show 150 = 12 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (311 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (311 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_311 :
    recurrence4Scalar2First.coeff 311 =
      (((((12175168216780580082 * 10 ^ 70 +
        7735052475375846848082053269772873398716941647172002690693294016802110) * 10 ^ 70 +
        0060548593976345109742375328250887694236513533312386660294216915681944) * 10 ^ 70 +
        8518585240903512282339098451346565936847761413448978343096549522410792) * 10 ^ 70 +
        3299629090701935298037545094063041412226022766044300528658757293064812) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (311 - x)) = _
  rw [show 312 = 1 +
    311 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 151 = 12 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (312 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (312 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_312 :
    recurrence4Scalar2First.coeff 312 =
      -(((((8098143510143236684 * 10 ^ 70 +
        8055840793919836154445646217815034629562610609510234212389316809357907) * 10 ^ 70 +
        7914938651684249482273063947582934467915648728903257245833558909907031) * 10 ^ 70 +
        9911996994905186649353123174817590950434037506542993558143264393238467) * 10 ^ 70 +
        3206753206571144868466872498849312856774012924364887256399539600408941) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (312 - x)) = _
  rw [show 313 = 1 +
    312 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 312 = 32 +
      280 by norm_num, Finset.sum_range_add]
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
    rw [show 152 = 12 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (313 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (313 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_313 :
    recurrence4Scalar2First.coeff 313 =
      (((((5089910867474364990 * 10 ^ 70 +
        5958993229029433504712860778693664250830574097421726727796508882702018) * 10 ^ 70 +
        0702469414396354375558201316491003897047941727526738805149179111356111) * 10 ^ 70 +
        0612399222333256161029809408980566833754241737177893533107215260573602) * 10 ^ 70 +
        0016663649130031015753005377266830233171205456675176556419881083968583) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (313 - x)) = _
  rw [show 314 = 1 +
    313 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 313 = 32 +
      281 by norm_num, Finset.sum_range_add]
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
    rw [show 153 = 12 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (314 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (314 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_314 :
    recurrence4Scalar2First.coeff 314 =
      -(((((3061016630163676945 * 10 ^ 70 +
        6323744787306049395997734615059879128942193621677252199730014036861232) * 10 ^ 70 +
        7750302883643697325871364152096307436905355418590636286888252400795970) * 10 ^ 70 +
        0385507372902447655787983649318208583934310755747992944421519099716440) * 10 ^ 70 +
        4078539531312252468849473459427664676259452939654329796143731181015021) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (314 - x)) = _
  rw [show 315 = 1 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
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
    rw [show 154 = 12 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (315 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (315 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_315 :
    recurrence4Scalar2First.coeff 315 =
      (((((1774040278527762005 * 10 ^ 70 +
        0292318901181587883851879098927579324341860201964239288604515350058777) * 10 ^ 70 +
        5211586592983144173276340280996551099907607760428291578135902095277738) * 10 ^ 70 +
        8313382364787040094594529424194805787432850385129402814562844018316874) * 10 ^ 70 +
        7638375202161871710010947221637019081628489480757983650312684542406562) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (315 - x)) = _
  rw [show 316 = 1 +
    315 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 315 = 32 +
      283 by norm_num, Finset.sum_range_add]
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
    rw [show 155 = 12 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (316 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (316 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_316 :
    recurrence4Scalar2First.coeff 316 =
      -(((((995115844259452310 * 10 ^ 70 +
        5661644728926828482527323196400277508459047395278126501995212677982428) * 10 ^ 70 +
        9856195254095109285600271049617787676644763817025741964474431158432181) * 10 ^ 70 +
        9234531170326314234032738841914581746771639463040832993902769436871876) * 10 ^ 70 +
        2465935207341608233172134466723801721628067849554556159780500457204218) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (316 - x)) = _
  rw [show 317 = 1 +
    316 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 316 = 32 +
      284 by norm_num, Finset.sum_range_add]
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
    rw [show 156 = 12 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (317 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (317 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_317 :
    recurrence4Scalar2First.coeff 317 =
      (((((541642068458239220 * 10 ^ 70 +
        6421351687260349497718295915418039028318658498777710162511897149468522) * 10 ^ 70 +
        4346553112788279220203100304780687694471384015436694562606641836443757) * 10 ^ 70 +
        0434344717923347784931325824036924734414640673335764747607697885600532) * 10 ^ 70 +
        4646708304203300676387846411567552724929279031570201740855459997473192) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (317 - x)) = _
  rw [show 318 = 1 +
    317 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 317 = 32 +
      285 by norm_num, Finset.sum_range_add]
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
    rw [show 157 = 12 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (318 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (318 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_318 :
    recurrence4Scalar2First.coeff 318 =
      -(((((286471377129265032 * 10 ^ 70 +
        0232206181320273295885859723497760320439783158904899453961232627744390) * 10 ^ 70 +
        4218283091504140010376187929121870211842254082640263558792290240122494) * 10 ^ 70 +
        0602326130990485902307349829943443883189666056446954676348079013125777) * 10 ^ 70 +
        0543611629966592362910480495935216025157407742955420862299655000767277) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (318 - x)) = _
  rw [show 319 = 1 +
    318 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 318 = 32 +
      286 by norm_num, Finset.sum_range_add]
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
    rw [show 158 = 12 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (319 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (319 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_319 :
    recurrence4Scalar2First.coeff 319 =
      (((((147292756183363980 * 10 ^ 70 +
        4160840229423160112691425548338441018038695294080599370871497031185115) * 10 ^ 70 +
        9235743449153701602191340192580183420142632515001930807406207448716202) * 10 ^ 70 +
        4894639041699539348210191129840045187098083022490561590658269737315904) * 10 ^ 70 +
        7761627147008659210908805553878846132150657902327603711768984909725967) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (319 - x)) = _
  rw [show 320 = 1 +
    319 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 319 = 32 +
      287 by norm_num, Finset.sum_range_add]
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
    rw [show 159 = 12 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (320 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (320 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_320 :
    recurrence4Scalar2First.coeff 320 =
      -(((((73595646832986639 * 10 ^ 70 +
        4968378449120169232205436158248773434206101122911373597626612233759666) * 10 ^ 70 +
        2170680552492845061597077605670722342417957881756031024032178431023023) * 10 ^ 70 +
        2061653890298502585035342956696927048163833660292897454853800129896979) * 10 ^ 70 +
        1471106043105545077373134575464770955045044515360392059394857950888034) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (320 - x)) = _
  rw [show 321 = 1 +
    320 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 320 = 32 +
      288 by norm_num, Finset.sum_range_add]
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
    rw [show 160 = 12 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (321 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (321 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_321 :
    recurrence4Scalar2First.coeff 321 =
      (((((35690116032128885 * 10 ^ 70 +
        6100482838622274617228250295545411171833998863351046010374788135947669) * 10 ^ 70 +
        0081378780728721565767407331721448555331682567773363263758275437477875) * 10 ^ 70 +
        4736992923196106674246201944491895138069995765591901742942028919272034) * 10 ^ 70 +
        1438664849704082717296151665494177975561181794377299310389192438062510) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (321 - x)) = _
  rw [show 322 = 1 +
    321 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 321 = 32 +
      289 by norm_num, Finset.sum_range_add]
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
    rw [show 161 = 12 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (322 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (322 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_322 :
    recurrence4Scalar2First.coeff 322 =
      -(((((16758909961233988 * 10 ^ 70 +
        8083155797152062137404676904806035825915845003136868260424420775777413) * 10 ^ 70 +
        3299060595133492481778444928075518890217402761104212862918161532475232) * 10 ^ 70 +
        1143239597114865140188382256597914484148998092867748496550980057349481) * 10 ^ 70 +
        6243394717266348780480073156825985877309461674846334992903459749905450) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (322 - x)) = _
  rw [show 323 = 1 +
    322 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 322 = 32 +
      290 by norm_num, Finset.sum_range_add]
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
    rw [show 162 = 12 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (323 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (323 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_323 :
    recurrence4Scalar2First.coeff 323 =
      (((((7590028474645244 * 10 ^ 70 +
        5842401560757735283608318704991931590274329834939438406064779196257943) * 10 ^ 70 +
        5598523689040597603532520589421042428726880074383990437767085926372315) * 10 ^ 70 +
        3124587362395922372838943878497303880403997793056708854874827821983759) * 10 ^ 70 +
        0599683270142624781303789379816956504818557947811030135329307310775676) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (323 - x)) = _
  rw [show 324 = 1 +
    323 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 323 = 32 +
      291 by norm_num, Finset.sum_range_add]
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
    rw [show 163 = 12 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (324 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (324 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_324 :
    recurrence4Scalar2First.coeff 324 =
      -(((((3294208595442310 * 10 ^ 70 +
        6650626767543319914813332433382009918120083594600365352352024903828627) * 10 ^ 70 +
        2008882877009908301703072640033879554572580232477989781072506156197049) * 10 ^ 70 +
        6749002115160206593806290431082509188314930672084114432752761522831558) * 10 ^ 70 +
        6837415753679247277208660681406255124433347761515258845791929598203893) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (324 - x)) = _
  rw [show 325 = 1 +
    324 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 324 = 32 +
      292 by norm_num, Finset.sum_range_add]
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
    rw [show 164 = 12 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (325 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (325 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_325 :
    recurrence4Scalar2First.coeff 325 =
      (((((1355250264614926 * 10 ^ 70 +
        9171676662527549037188703825914475563033965774413249824140440181206246) * 10 ^ 70 +
        7363702974204881596404829093443682814471891495471679890700512607874969) * 10 ^ 70 +
        5999119450111036992751100061974113451031129634957092403026040968119047) * 10 ^ 70 +
        9101250934637101406868571182865464068822810616219223756870886990687138) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (325 - x)) = _
  rw [show 326 = 1 +
    325 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 325 = 32 +
      293 by norm_num, Finset.sum_range_add]
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
    rw [show 165 = 12 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (326 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (326 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_326 :
    recurrence4Scalar2First.coeff 326 =
      -(((((517900336187960 * 10 ^ 70 +
        8299028799251242138192922196894541449850273339386446838128295897003757) * 10 ^ 70 +
        4344334217377342227944820692072927803771592917050179783527916348453975) * 10 ^ 70 +
        3901041666324367790701731570963400703960552590876038203720518492916460) * 10 ^ 70 +
        5399133221402149833886450763777665794650331478105381894129423030693704) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (326 - x)) = _
  rw [show 327 = 1 +
    326 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 326 = 32 +
      294 by norm_num, Finset.sum_range_add]
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
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (327 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (327 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_327 :
    recurrence4Scalar2First.coeff 327 =
      (((((175974047097632 * 10 ^ 70 +
        2952304925611128469816892395146589670630866594699380824548254488253128) * 10 ^ 70 +
        2993990779493950964160392204580526096341882277696477043997726251154582) * 10 ^ 70 +
        4091873381778719973733252970290612298510842982979717345454325597672421) * 10 ^ 70 +
        3204017272147044116540251669350021242344659562601181983066615068072124) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (327 - x)) = _
  rw [show 328 = 1 +
    327 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 327 = 32 +
      295 by norm_num, Finset.sum_range_add]
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
    rw [show 167 = 12 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (328 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (328 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_328 :
    recurrence4Scalar2First.coeff 328 =
      -(((((46861528527082 * 10 ^ 70 +
        2310272360264606598189485857633747428511186194699796993116084888014254) * 10 ^ 70 +
        6461238048334946418828369715100379615818238836816898764545498696268354) * 10 ^ 70 +
        7260846246878073911081254526291849990267089731148484785489618120404000) * 10 ^ 70 +
        3100662265371943511269480198598802123398023738217445796970961392181863) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (328 - x)) = _
  rw [show 329 = 1 +
    328 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 328 = 32 +
      296 by norm_num, Finset.sum_range_add]
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
    rw [show 168 = 12 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (329 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (329 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_329 :
    recurrence4Scalar2First.coeff 329 =
      (((((3955798375900 * 10 ^ 70 +
        8626464551702442571772659495537879292328209654484622801453672047483044) * 10 ^ 70 +
        7733478192864362536066641347604026303785833990923870137358400518133306) * 10 ^ 70 +
        9170014078491229460435869894393585349192708093240899267193273661224479) * 10 ^ 70 +
        3222063661971594901413873214168470719161815395239616390155681440343690) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (329 - x)) = _
  rw [show 330 = 1 +
    329 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 329 = 32 +
      297 by norm_num, Finset.sum_range_add]
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
    rw [show 169 = 12 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (330 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (330 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_330 :
    recurrence4Scalar2First.coeff 330 =
      (((((6819191256019 * 10 ^ 70 +
        3415079448887084505802595244983502317446385988656974157803413361304795) * 10 ^ 70 +
        4309783831831415725033735742157786489058336734023253463774850604917867) * 10 ^ 70 +
        5258163893911022905825622275076459445517849817517116491700744714700381) * 10 ^ 70 +
        1674471647558065863404584758094696032067521668983682244268776535585021) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (330 - x)) = _
  rw [show 331 = 1 +
    330 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 330 = 32 +
      298 by norm_num, Finset.sum_range_add]
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
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (331 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (331 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_331 :
    recurrence4Scalar2First.coeff 331 =
      -(((((7180214045773 * 10 ^ 70 +
        6469905255128991079674242599916321030676305219134168549089360095275210) * 10 ^ 70 +
        4743440347047991125464253119679711518023300502055287659784558825496173) * 10 ^ 70 +
        3403605022625336164722851352081541960097408859117875326365408026387782) * 10 ^ 70 +
        3530262621268105836945718666805767555629897581619053677549456549221423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (331 - x)) = _
  rw [show 332 = 1 +
    331 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 331 = 32 +
      299 by norm_num, Finset.sum_range_add]
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
    rw [show 171 = 12 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (332 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (332 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_332 :
    recurrence4Scalar2First.coeff 332 =
      (((((5106960905947 * 10 ^ 70 +
        8038914781404936882365158931170357922380355563042531740364355743866575) * 10 ^ 70 +
        2433555920891902208357409711447724757646087023423628297149415979229536) * 10 ^ 70 +
        9992376430519160906826254754537541085973058140400223964961418229698524) * 10 ^ 70 +
        0972951817424841673288955516067485649339773092797106679775954659279337) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (332 - x)) = _
  rw [show 333 = 1 +
    332 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 332 = 32 +
      300 by norm_num, Finset.sum_range_add]
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
    rw [show 172 = 12 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (333 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (333 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_333 :
    recurrence4Scalar2First.coeff 333 =
      -(((((3113558776874 * 10 ^ 70 +
        9476788402615279745281746153551643769465283437501581428818297296645710) * 10 ^ 70 +
        7301952556052617216325596214798990130002103448769186045748798044467698) * 10 ^ 70 +
        0697406956473641131511202821387277775400979798224084458069862862452352) * 10 ^ 70 +
        3633216505804935244054473363588892651368851459376250951547976141394995) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (333 - x)) = _
  rw [show 334 = 1 +
    333 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 333 = 32 +
      301 by norm_num, Finset.sum_range_add]
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
    rw [show 173 = 12 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (334 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (334 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_334 :
    recurrence4Scalar2First.coeff 334 =
      (((((1737048334340 * 10 ^ 70 +
        7901169640405947785689735458357924369075570619659661935776284842301018) * 10 ^ 70 +
        3378643697122758347168936357247098598492467272153185619833173367403188) * 10 ^ 70 +
        0999571595075349724065456491977312718346482459521931804550457196577313) * 10 ^ 70 +
        3919539352262519383670174912789028817655231785085696349933526257691519) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (334 - x)) = _
  rw [show 335 = 1 +
    334 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 334 = 32 +
      302 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 302 = 32 +
      270 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 12 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (335 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (335 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_335 :
    recurrence4Scalar2First.coeff 335 =
      -(((((911400922432 * 10 ^ 70 +
        3780746183571920353031222201238690060508677315433440564047913977988390) * 10 ^ 70 +
        0313893819670309343570977614917247897848113694630565528776807464035959) * 10 ^ 70 +
        8966940714706194878070866048598251860738341204591322142760044404224784) * 10 ^ 70 +
        1969710227523377225202589671483458715305829873341673881311196456879488) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (335 - x)) = _
  rw [show 336 = 1 +
    335 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 335 = 32 +
      303 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 303 = 32 +
      271 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 12 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (336 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (336 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_336 :
    recurrence4Scalar2First.coeff 336 =
      (((((456029114087 * 10 ^ 70 +
        2561504190004561051757328928247635886935569970243480949582215826433651) * 10 ^ 70 +
        4490414157956695278554291420221140258509140239991810093388432781063176) * 10 ^ 70 +
        7218129837167478571412872995519064824980952945982667000787877236686813) * 10 ^ 70 +
        5310962876017509298298422794638278051108553900987606063644295092394504) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (336 - x)) = _
  rw [show 337 = 1 +
    336 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 336 = 32 +
      304 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 304 = 32 +
      272 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 12 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (337 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (337 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_337 :
    recurrence4Scalar2First.coeff 337 =
      -(((((219322758856 * 10 ^ 70 +
        5821221414081687747880996245136027257112043250242764716126512547328606) * 10 ^ 70 +
        7072104768138587200860541119648538972375608194433381236116168877128059) * 10 ^ 70 +
        0735303928047269230224576737101120124997827439244015706214910667950923) * 10 ^ 70 +
        2546230941835347084707100164050246413666351200049287350078591453749934) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (337 - x)) = _
  rw [show 338 = 1 +
    337 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 337 = 32 +
      305 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 305 = 32 +
      273 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 12 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (338 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (338 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_338 :
    recurrence4Scalar2First.coeff 338 =
      (((((101866625773 * 10 ^ 70 +
        5438113144348095773763219920049485757226062244495267348139197871469459) * 10 ^ 70 +
        1008888705906506922812297767294803569943411936822431495519381434562319) * 10 ^ 70 +
        7406757009082850070037238521666280252818948469696002095051767535256613) * 10 ^ 70 +
        8792302282201390775659676957048921774554658053701683253763337152730706) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (338 - x)) = _
  rw [show 339 = 1 +
    338 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 338 = 32 +
      306 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 306 = 32 +
      274 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 12 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (339 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (339 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_339 :
    recurrence4Scalar2First.coeff 339 =
      -(((((45821836211 * 10 ^ 70 +
        2644982841869330820378883809108816671346481029445917707377458615306018) * 10 ^ 70 +
        5419125276005828918552014508958118159647290615832325321685623878215483) * 10 ^ 70 +
        5578150640482929703924106500986762732272135412018376433559052376949272) * 10 ^ 70 +
        8016513052915934019103338647711387625568835636296762149686132194966064) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (339 - x)) = _
  rw [show 340 = 1 +
    339 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 339 = 32 +
      307 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 307 = 32 +
      275 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 12 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (340 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (340 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_340 :
    recurrence4Scalar2First.coeff 340 =
      (((((19993921057 * 10 ^ 70 +
        4620260964140872366280149552802330998786271186151988912608775308459923) * 10 ^ 70 +
        3753141587212623124672065619378103387394479237927643386765612169094163) * 10 ^ 70 +
        3303889520886840361767571278894895353186764146323696011205682233137401) * 10 ^ 70 +
        2808329882121152135099820657552557543116127253472916376147418224057199) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (340 - x)) = _
  rw [show 341 = 1 +
    340 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 340 = 32 +
      308 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 308 = 32 +
      276 by norm_num, Finset.sum_range_add]
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
    rw [show 180 = 12 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (341 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (341 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_341 :
    recurrence4Scalar2First.coeff 341 =
      -(((((8468115905 * 10 ^ 70 +
        7143575632558719986117882049960669938008196932431770255520757516925692) * 10 ^ 70 +
        1306392140233117356578851366733677213520823431065455225662321494131644) * 10 ^ 70 +
        4126205909782931342702041782598110485988181483951836897448657003484951) * 10 ^ 70 +
        7891698102487028914309780553673482538453344087255127660815324059823713) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (341 - x)) = _
  rw [show 342 = 1 +
    341 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 341 = 32 +
      309 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 309 = 32 +
      277 by norm_num, Finset.sum_range_add]
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
    rw [show 181 = 12 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (342 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (342 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_342 :
    recurrence4Scalar2First.coeff 342 =
      (((((3480530075 * 10 ^ 70 +
        3859034482022337167681380743747342871564819970099370325974588290014554) * 10 ^ 70 +
        3356580797375394941867084553074602254979366034791518745931359671931644) * 10 ^ 70 +
        1899964889413460142049912701693445663365327340377854296455073913017836) * 10 ^ 70 +
        9882382689438478007935301704626236603748334641730589472418540287898631) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (342 - x)) = _
  rw [show 343 = 1 +
    342 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 342 = 32 +
      310 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 310 = 32 +
      278 by norm_num, Finset.sum_range_add]
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
    rw [show 182 = 12 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (343 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (343 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_343 :
    recurrence4Scalar2First.coeff 343 =
      -(((((1386690664 * 10 ^ 70 +
        2089697438102877958906683266521609250973611011784850669398063614723509) * 10 ^ 70 +
        8963058516249759290194891066175799928261452181828654096358143298381628) * 10 ^ 70 +
        9740853110878690278484139861409756168515407559684456235115411244290363) * 10 ^ 70 +
        9758227171691197030955119786523100939820656130275960535330795285564629) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (343 - x)) = _
  rw [show 344 = 1 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 12 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (344 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (344 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_344 :
    recurrence4Scalar2First.coeff 344 =
      (((((534296033 * 10 ^ 70 +
        7972591813341252098680661270004637076747885397981222412755213981807035) * 10 ^ 70 +
        4490115552673161266730237370334382155245875785897825896274408213876026) * 10 ^ 70 +
        9704065455777915854261720821206352254560957627182075482351577171924369) * 10 ^ 70 +
        2560118253732972892385650533760741701671900697455990923786947641159407) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (344 - x)) = _
  rw [show 345 = 2 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 11 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (345 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (345 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_345 :
    recurrence4Scalar2First.coeff 345 =
      -(((((198281986 * 10 ^ 70 +
        7577515081193100958506774746869124744358485375160859564981876260837425) * 10 ^ 70 +
        8139953396868368504051868153806761706688252946216222130851230410286036) * 10 ^ 70 +
        5999694099360468817916893497530345144750658251520055695206156871292385) * 10 ^ 70 +
        1268847082059231743556045166824125813541481078323169630733076380471475) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (345 - x)) = _
  rw [show 346 = 3 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 10 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (346 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (346 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_346 :
    recurrence4Scalar2First.coeff 346 =
      (((((70377501 * 10 ^ 70 +
        0811609209902136025049173923095335191061067364323341783205228161566089) * 10 ^ 70 +
        6759340687949015468292919424138803290813286869482466108957688813782799) * 10 ^ 70 +
        7693355041352027810962898329835258660097866768998715339184296796791414) * 10 ^ 70 +
        8358046087921685537823756405976098129406442273422653839259054449931276) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (346 - x)) = _
  rw [show 347 = 4 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 9 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (347 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (347 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_347 :
    recurrence4Scalar2First.coeff 347 =
      -(((((23591291 * 10 ^ 70 +
        7710060965016480058057430798348361427044957119136377055924931799457820) * 10 ^ 70 +
        3558918485073431606765470080911472170100166588472109158714661909323326) * 10 ^ 70 +
        0579882828197262485571053889703201122373269302615349632917481809630638) * 10 ^ 70 +
        0995143446864770629266494114942240475760803527080076594627359671004354) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (347 - x)) = _
  rw [show 348 = 5 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 8 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (348 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (348 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_348 :
    recurrence4Scalar2First.coeff 348 =
      (((((7284371 * 10 ^ 70 +
        4290018026451784054241624966788458055101279217533810534219206186797619) * 10 ^ 70 +
        3553242437400141723078023533823796956386571895272437518993034075853094) * 10 ^ 70 +
        7378885713362743071810259281680897730206553970884387748237708138744737) * 10 ^ 70 +
        4081966013311754782069215054382556340437414404493624974792686811074070) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (348 - x)) = _
  rw [show 349 = 6 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 7 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (349 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (349 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_349 :
    recurrence4Scalar2First.coeff 349 =
      -(((((1953047 * 10 ^ 70 +
        7793996968756188099228658622235032935010779398260229514624830805950977) * 10 ^ 70 +
        3022744515809566713368807319542504896334172373717631374207531730710411) * 10 ^ 70 +
        3342949913164337042169293535306457754750750310356452521255815418165408) * 10 ^ 70 +
        4683489435224660354191094918198853532660395260594458271503865492828631) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (349 - x)) = _
  rw [show 350 = 7 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 6 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (350 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (350 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_350 :
    recurrence4Scalar2First.coeff 350 =
      (((((370619 * 10 ^ 70 +
        2844453445411448679489619280881323168788650476996066341842127852358494) * 10 ^ 70 +
        3335889088722758052290952125707903241096649669071953262356396079361114) * 10 ^ 70 +
        1649395593419588304027464809810449649227222949535185038393386820883842) * 10 ^ 70 +
        3898014307592677625591322849540024067110003870661091814961506069479236) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (350 - x)) = _
  rw [show 351 = 8 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 5 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (351 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (351 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_351 :
    recurrence4Scalar2First.coeff 351 =
      (((((21024 * 10 ^ 70 +
        2292409815949978564251680950054596924440430153716012077157681160457039) * 10 ^ 70 +
        9312698567853861230503112303733071963639394633415937289955156163817426) * 10 ^ 70 +
        2098196739725551506635945307503425891333263839702869175643662619422845) * 10 ^ 70 +
        9163214653608786614465581291704115572092320428678773836347419063734786) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (351 - x)) = _
  rw [show 352 = 9 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 4 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (352 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (352 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_352 :
    recurrence4Scalar2First.coeff 352 =
      -(((((76024 * 10 ^ 70 +
        8404827832322985609679003890882473491510392317779005163718962277114506) * 10 ^ 70 +
        9602993644889875992649948995615050545481897387581121165550806318563419) * 10 ^ 70 +
        8973201508876006075236594419857753307800653265795352299571374201445381) * 10 ^ 70 +
        7704769766865689931672152892370573290269870500019223951513165169624248) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (352 - x)) = _
  rw [show 353 = 10 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 3 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (353 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (353 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_353 :
    recurrence4Scalar2First.coeff 353 =
      (((((56638 * 10 ^ 70 +
        3101929113768879121876696448194079940857318321546902117275752484846272) * 10 ^ 70 +
        8688132940603689683931976058078508267648497647058033633007902743363595) * 10 ^ 70 +
        9617064640272223536469790337217639720583563617295917499900140733106942) * 10 ^ 70 +
        7046341438434237900426358539216401624032732111868779494492425290746685) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (353 - x)) = _
  rw [show 354 = 11 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 2 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (354 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (354 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_354 :
    recurrence4Scalar2First.coeff 354 =
      -(((((32534 * 10 ^ 70 +
        6690549050363454682373009795967482359023732992523373125208262534156908) * 10 ^ 70 +
        3751944622998474587834215573015499298680923181106323530354871076787852) * 10 ^ 70 +
        6047652768658851443628917558344770734128752378379097138864704967513250) * 10 ^ 70 +
        8202511575224380496846971155005724244040279335487486372412697045853415) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (354 - x)) = _
  rw [show 355 = 12 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
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
    rw [show 183 = 1 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (355 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (355 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_355 :
    recurrence4Scalar2First.coeff 355 =
      (((((16615 * 10 ^ 70 +
        9448881222827856839309751813730840024388396955754883969870810952658299) * 10 ^ 70 +
        7232027915419667344815925888953483873167063817098748214662727490786380) * 10 ^ 70 +
        1951522647152266231644290371175899774657494107856646917626481723997985) * 10 ^ 70 +
        5496682315436745703000622533078956988708783786037130925845234318384625) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (355 - x)) = _
  rw [show 356 = 13 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (356 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (356 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_356 :
    recurrence4Scalar2First.coeff 356 =
      -(((((7907 * 10 ^ 70 +
        7666635271160424572186450278174248444964403291257375369400253859751503) * 10 ^ 70 +
        2129063077689193850731862204254315873182096047082966066498665544367081) * 10 ^ 70 +
        9648349382289714247118238883958759130206828780562086300190066299037941) * 10 ^ 70 +
        7563723118944998273142883951011041353752364470207021607410832622503824) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (356 - x)) = _
  rw [show 357 = 14 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 31 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (357 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (357 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_357 :
    recurrence4Scalar2First.coeff 357 =
      (((((3580 * 10 ^ 70 +
        5129935116848842143584191247814256944789645984884771144148191213237844) * 10 ^ 70 +
        9049827350256511750369714953636750648092334001125166874737595935665823) * 10 ^ 70 +
        0938181794421500869288648710718714362210840588542740951120548547899877) * 10 ^ 70 +
        4562885420655531681997138179700200647961536050189555576749408385921709) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (357 - x)) = _
  rw [show 358 = 15 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 30 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (358 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (358 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_358 :
    recurrence4Scalar2First.coeff 358 =
      -(((((1558 * 10 ^ 70 +
        2643507630308334802489653233998508362431422760718947829929828858118771) * 10 ^ 70 +
        0663590557783177286084015897755363917582358595139830041163968764945946) * 10 ^ 70 +
        4353907664739787513702003039571740369811789710590155859020417079002255) * 10 ^ 70 +
        7834238367444264414757052736730378334894327992024857591655019629804808) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (358 - x)) = _
  rw [show 359 = 16 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 29 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (359 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (359 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_359 :
    recurrence4Scalar2First.coeff 359 =
      (((((655 * 10 ^ 70 +
        0426735417591091115490380661994423318200891108923866884387519109628487) * 10 ^ 70 +
        9279436394164877912391749689633108498208155438727268566458944915412492) * 10 ^ 70 +
        5329429299024993548697767063928205821919755236498949948851595012626053) * 10 ^ 70 +
        7652921457965690724604296597843740884853032770523592541821395265870164) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (359 - x)) = _
  rw [show 360 = 17 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 28 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (360 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (360 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_360 :
    recurrence4Scalar2First.coeff 360 =
      -(((((266 * 10 ^ 70 +
        4035468829613767150650755057360214216784009928203877220910993369265133) * 10 ^ 70 +
        8063511331056203745060982736487902247654163534884221360642713965364136) * 10 ^ 70 +
        1909704975991294799346476544575894230460515157351336736776430964798852) * 10 ^ 70 +
        7828713651726611938757962475165638327265548971344296691010498962059944) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (360 - x)) = _
  rw [show 361 = 18 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 27 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (361 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (361 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_361 :
    recurrence4Scalar2First.coeff 361 =
      (((((104 * 10 ^ 70 +
        7367886806253447649542393508517861692629943450194045165491959039664485) * 10 ^ 70 +
        9336042604052816412425671437076792625097778487556568802065997961392462) * 10 ^ 70 +
        8269917275028641666284563541160760106575075688870675835334032307473957) * 10 ^ 70 +
        7798706978193503212346185009749905934805342573446515945076961400460213) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (361 - x)) = _
  rw [show 362 = 19 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 26 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (362 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (362 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_362 :
    recurrence4Scalar2First.coeff 362 =
      -(((((39 * 10 ^ 70 +
        6814814764698048713091032937688965243619954326314654224076678531362333) * 10 ^ 70 +
        5881614081805996130934260989374656251128864554744835987702854023612022) * 10 ^ 70 +
        5858403261069192414969762795689906819470608276496170545602862133013788) * 10 ^ 70 +
        1881911142984351554415514285600031694310949254334325015995499025039859) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (362 - x)) = _
  rw [show 363 = 20 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 25 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (363 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (363 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_363 :
    recurrence4Scalar2First.coeff 363 =
      (((((14 * 10 ^ 70 +
        4017014516693052025750350416388251565360563287543506821309215334408529) * 10 ^ 70 +
        2666235075192456178208583463025659768501687137108540272912759227477608) * 10 ^ 70 +
        1552862748760004337699114648690838987461676077023985197462912727033719) * 10 ^ 70 +
        6813227640365097686293357489379422990226174980650897857588775053258297) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (363 - x)) = _
  rw [show 364 = 21 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 24 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (364 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (364 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_364 :
    recurrence4Scalar2First.coeff 364 =
      -(((((4 * 10 ^ 70 +
        9552796448004741978162894467890920256184511994165161142100983062382187) * 10 ^ 70 +
        2486850975366320735147968160202608443682656731017130772513253139261609) * 10 ^ 70 +
        5302417958306139799245688427936766204182406656596217146171931132247088) * 10 ^ 70 +
        5337812150347290443474698270541979480931826952789042597567938258945679) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (364 - x)) = _
  rw [show 365 = 22 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 23 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (365 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (365 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_365 :
    recurrence4Scalar2First.coeff 365 =
      (((((1 * 10 ^ 70 +
        5862447138927228530002325100220948301014361762957916611946391485374073) * 10 ^ 70 +
        1727333697300392438169553971580211370272816238487924708207530342234707) * 10 ^ 70 +
        0131418007106570143878011626690757622362068749286993294286532883290131) * 10 ^ 70 +
        2084965041767019186442628336422060987860656532309385367049059076529286) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (365 - x)) = _
  rw [show 366 = 23 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 22 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (366 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (366 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_366 :
    recurrence4Scalar2First.coeff 366 =
      -((((4543594034307845937095921993300058545761946488455553719582327157756807 * 10 ^ 70 +
        5281883967293960440357876459861342540411580160988983434918846913381049) * 10 ^ 70 +
        2653347653272239938482637588696975538057714276783060012218142660389304) * 10 ^ 70 +
        4610973859144085550911644924999513635483756290008494675620477087787738) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (366 - x)) = _
  rw [show 367 = 24 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 21 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (367 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (367 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_367 :
    recurrence4Scalar2First.coeff 367 =
      ((((1048753576605666811572679606039613877865937082837999037399037068666268 * 10 ^ 70 +
        7056777777190415019194323383661167624192403785696681885062132849515306) * 10 ^ 70 +
        4030132566901394076747126730310260620863698549628727480887596111444959) * 10 ^ 70 +
        6352747566316993537076990760232120095903740505691048290307528061746383) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (367 - x)) = _
  rw [show 368 = 25 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 20 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (368 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (368 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_368 :
    recurrence4Scalar2First.coeff 368 =
      -((((110576430145268469167238609588123085791880914774983608806680290780702 * 10 ^ 70 +
        5862186087906973304090547496627816065010434091035224674413454078408301) * 10 ^ 70 +
        0887056260896600491821878274726641288504989484367441520475506214296359) * 10 ^ 70 +
        8546395572947631890933045342076739543582496305535252821320701442919997) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (368 - x)) = _
  rw [show 369 = 26 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 19 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (369 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (369 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_369 :
    recurrence4Scalar2First.coeff 369 =
      -((((72536958049755527513870068928810325647460804335966727226409496414349 * 10 ^ 70 +
        1489251068628180926342945208352691891341354729157744611091691668717407) * 10 ^ 70 +
        8289011163590703266577049843221511581388083349312797568161394729047917) * 10 ^ 70 +
        7866048431401819988557950373390570865717639506066020581609783003828015) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (369 - x)) = _
  rw [show 370 = 27 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 18 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (370 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (370 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_370 :
    recurrence4Scalar2First.coeff 370 =
      ((((70221309328128595609945611946148285258419577925412837169273643913677 * 10 ^ 70 +
        9343650151894878554796196617996156730435846301944291110127173719226378) * 10 ^ 70 +
        3589344031256572588640748251880684630220469598571192053774066742842884) * 10 ^ 70 +
        9012652181328595328992767830888336266625868821455886005055206439521926) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (370 - x)) = _
  rw [show 371 = 28 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 17 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (371 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (371 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_371 :
    recurrence4Scalar2First.coeff 371 =
      -((((41438190229352366926631260918726071872638749013853075687908074958367 * 10 ^ 70 +
        1206610815624837595886440323802626109607670543645373485784306490490106) * 10 ^ 70 +
        3780061487984503748254689730729219754923691252426957538672533573151498) * 10 ^ 70 +
        3668250587776089848161065790046198087168092006051131085459059514244432) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (371 - x)) = _
  rw [show 372 = 29 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 16 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (372 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (372 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_372 :
    recurrence4Scalar2First.coeff 372 =
      ((((20397107379687218397104305656409755538771244207754938697448650932095 * 10 ^ 70 +
        1701727970051868215715852230331879853131672539172902468591110858659615) * 10 ^ 70 +
        6341007809024521879212593760564939528501335721996331292024422256365937) * 10 ^ 70 +
        0826522661205807120342761599337339451028061417001982313803911302864130) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (372 - x)) = _
  rw [show 373 = 30 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 15 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (373 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (373 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_373 :
    recurrence4Scalar2First.coeff 373 =
      -((((9027332222992998465160093876955259602225643641862949082844367258797 * 10 ^ 70 +
        7692924079007134507896574537717031183360772989533884678853185029940331) * 10 ^ 70 +
        6440462702371041706862323161716909300847858379168488244214283526501383) * 10 ^ 70 +
        8105059874237378995136386339569891097603489049746251211562823294988527) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (373 - x)) = _
  rw [show 374 = 31 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 14 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (374 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (374 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_374 :
    recurrence4Scalar2First.coeff 374 =
      ((((3695489088456919715512143261316964143871181162782846229185121482508 * 10 ^ 70 +
        3726194472380145919269158580654707156917226257009298785295167209512434) * 10 ^ 70 +
        2736616699779278422820351259428314296770127772591388805558871607395136) * 10 ^ 70 +
        0964809481809466266942197930691550656555530170150255592158577671511046) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (374 - x)) = _
  rw [show 375 = 32 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 13 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (375 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (375 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_375 :
    recurrence4Scalar2First.coeff 375 =
      -((((1415834616073323971822809241828577837010846656429121570741854825759 * 10 ^ 70 +
        9282824404851455133647644282107557392751645862838260721376753415047962) * 10 ^ 70 +
        7709205719103042492603941141979155798983415905874875846427939340597316) * 10 ^ 70 +
        3507363613998556326538972838785558132330570203223207984588321330710538) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (375 - x)) = _
  rw [show 376 = 33 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 12 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (376 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (376 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_376 :
    recurrence4Scalar2First.coeff 376 =
      ((((509288026247192895669255812565014487570221869363206697470520514175 * 10 ^ 70 +
        4650998378572053670233488441999580074915389219779155115079468729408238) * 10 ^ 70 +
        4615043851362014193054512970510673113782922681935619253794875781550158) * 10 ^ 70 +
        5762477399062820518408719010616556839560997427268357489445548921933250) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (376 - x)) = _
  rw [show 377 = 34 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 11 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (377 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (377 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_377 :
    recurrence4Scalar2First.coeff 377 =
      -((((171378877498012194157776756332609228293867200974106577845754237835 * 10 ^ 70 +
        2108988931230888692015997863366940613756320784196279474870358645601782) * 10 ^ 70 +
        1004117586887244302902969685709079667479461686649511631518238555584430) * 10 ^ 70 +
        7373633874255848702831931431866839544555294374428833395425384194843824) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (377 - x)) = _
  rw [show 378 = 35 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 10 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (378 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (378 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_378 :
    recurrence4Scalar2First.coeff 378 =
      ((((53290090409385014208321018903153222650351136490927876319512716014 * 10 ^ 70 +
        3287355530017630387648150178816585746688402876985705916214727455165446) * 10 ^ 70 +
        5425569421159316740651855423889739088952511168651264586328112090156356) * 10 ^ 70 +
        7320857212913575899602903746696164336851991980482315201198572661961556) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (378 - x)) = _
  rw [show 379 = 36 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 9 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (379 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (379 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_379 :
    recurrence4Scalar2First.coeff 379 =
      -((((14870396205980421851860769816278447304464053187303313306541894203 * 10 ^ 70 +
        3596008178540840443750767622913567072197640035412770902915606548580925) * 10 ^ 70 +
        7955861506461603707274003906504928782168702565100016190181818740771335) * 10 ^ 70 +
        6735105566731640436932542023207889077124658813961444474595233668982940) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (379 - x)) = _
  rw [show 380 = 37 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 8 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (380 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (380 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_380 :
    recurrence4Scalar2First.coeff 380 =
      ((((3446440543244035889545453204214247833255724805605579289550491284 * 10 ^ 70 +
        3870398614632200796790339278842853532136424151407780989784889823081085) * 10 ^ 70 +
        1003904211913016721424969724914922493713349331002282050771869516409961) * 10 ^ 70 +
        0194208193266655070584386409599393107766542890727311612580439880781745) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (380 - x)) = _
  rw [show 381 = 38 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 7 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (381 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (381 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_381 :
    recurrence4Scalar2First.coeff 381 =
      -((((477851474248902326731234011870993210011912974686808989949611405 * 10 ^ 70 +
        5434490845635971049214510582246645018964021901460550708106098973328751) * 10 ^ 70 +
        1105593086746032810567004335537995238694918929427590478792686337745211) * 10 ^ 70 +
        4651554345104340048124463691483419051596661573118551762153440040800393) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (381 - x)) = _
  rw [show 382 = 39 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 6 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2First_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (382 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (382 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_382 :
    recurrence4Scalar2First.coeff 382 =
      -((((109406951691816989711944340828812595762410916924578479489526936 * 10 ^ 70 +
        6837352861861235315738048264644408912574205975930094001830910647727511) * 10 ^ 70 +
        6571577334390745695157565706591702063216129502341794193962133311462537) * 10 ^ 70 +
        3775380507971414771956526112040138707666575729332716552304419516047139) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (382 - x)) = _
  rw [show 383 = 40 +
    343 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 343 = 32 +
      311 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 311 = 32 +
      279 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 279 = 32 +
      247 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 5 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
